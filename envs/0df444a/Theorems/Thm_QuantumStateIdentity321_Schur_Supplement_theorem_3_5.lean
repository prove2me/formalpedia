-- Prove2me | Theorems.Thm_QuantumStateIdentity321_Schur_Supplement_theorem_3_5
-- name    : QuantumStateIdentity321.Schur.Supplement.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:55:12.368283+00:00
-- url     : https://prove2.me/theorems/e4f0cbe7-5e92-45bc-b526-4e4e41660f6d
-- title:
--   Theorem 3.5 — completeness of Algorithm 2 with $k\ell=O((1-2\sqrt\varepsilon)^{-2}\log(2/\delta)\log(n/\delta))$ copies
-- statement:
--   Let $n\ge3$ and $d\ge2$, let $\varepsilon\in(0,1/4)$ and $\delta\in(0,1)$, and set $\gamma=\frac12-\sqrt\varepsilon$, $\tau=(7-2\varepsilon+\sqrt\varepsilon)/8$, $\ell=\lceil\log_3(2/\delta)\rceil$ and $k=\lceil(8/\gamma^2)\log(n\ell/\delta)\rceil$. Then Algorithm 2 is a two-outcome measurement that accepts every yes instance of $\mathrm{QSI}^\varepsilon_n$ with probability at least $1-\delta$. It consumes exactly $k\ell$ copies of each input state when $n$ is even, and $2k\ell$ copies of $|\psi_1\rangle$ and $k\ell$ of every other state when $n$ is odd, and there is an absolute constant $C$ with
--
--   $$
--   k\ell\le\frac{C}{(1-2\sqrt\varepsilon)^2}\,\log(2/\delta)\,\log(n/\delta).
--   $$
--
--   With Theorem 3.4 (1), Algorithm 2 solves $\mathrm{QSI}^\varepsilon_n$ with error $\delta$ using these copies.
--
--   **Formalization Note** The protocol is its accept effect, as in Theorem 3.4; the constant $C$ is quantified before $n,d,\varepsilon,\delta$.
--
--   Differences from the source:
--   - encoding: Algorithm 2 as a procedure → its accept effect alg2Effect, with validity 0 ≤ A ≤ I as a conjunct; reason: every procedure ending in accept/reject has such an effect; same algorithm
--   - reading: step 3, k = ⌈(8/γ²) log(nℓ/δ)⌉, after "n becomes even" for odd n → n is the number of input states (not the padded n + 1); reason: the procedure could be read either way; the input n gives fewer copies, the stronger claim
--   - generalization: at most 2kℓ copies of ψ₁ when n is odd → the exact counts 2kℓ for ψ₁ and kℓ for every other state; reason: exact counts imply the source's upper bound
--   - encoding: kℓ = O((1−2√ε)⁻² log(2/δ) log(n/δ)) → kℓ ≤ C (1−2√ε)⁻² log(2/δ) log(n/δ) with ∃ C > 0 before n, d, ε, δ; reason: the meaning of the O(·)
--   - encoding: indices $1,\dots,n$ → `Fin n`, label $i$ is the source's $i+1$; reason: Lean convention; same instances
-- source:
--   Shih-Han Hung, Ming-Hsien Tsai, STOC 2027 submission #321 (October 2026), Theorem 3.5, PDF/printed p.13, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/321.pdf

import Definitions.Def_QuantumStateIdentity321_Schur_Supplement_SwapMatching

namespace QuantumStateIdentity321.Schur.Supplement

open Matrix

/-- Theorem 3.5 (completeness), p.13: for `n ≥ 3`, `d ≥ 2`, `ε ∈ (0, 1/4)` and `δ ∈ (0, 1)`,
Algorithm 2 (with `τ = (7 − 2ε + √ε)/8`, `ℓ = ⌈log₃(2/δ)⌉`, `k = ⌈(8/γ²) log(nℓ/δ)⌉`,
`γ = 1/2 − √ε`) is a two-outcome measurement that accepts every yes instance with probability at
least `1 − δ`. It consumes exactly `kℓ` copies of each input state (`2kℓ` copies of `|ψ₁⟩` when
`n` is odd), and `kℓ ≤ C (1 − 2√ε)⁻² log(2/δ) log(n/δ)` for an absolute constant `C`. -/
theorem theorem_3_5 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n d : ℕ), 3 ≤ n → 2 ≤ d →
      ∀ ε δ : ℝ, 0 < ε → ε < 1 / 4 → 0 < δ → δ < 1 →
        IsValidEffect (alg2Effect n d (alg2Rounds δ) (alg2Copies n ε δ) (swapThreshold ε)) ∧
        (∀ ψ : Fin n → State d, (∀ i, ‖ψ i‖ = 1) → IsYesInstance ε ψ →
          1 - δ ≤ labelledAcceptProb
              (alg2Effect n d (alg2Rounds δ) (alg2Copies n ε δ) (swapThreshold ε))
              (alg2Label n (alg2Rounds δ) (alg2Copies n ε δ)) ψ) ∧
        (∀ i : Fin n, copyCount (alg2Label n (alg2Rounds δ) (alg2Copies n ε δ)) i =
          (if n % 2 = 1 ∧ i.val = 0 then 2 else 1) * (alg2Copies n ε δ * alg2Rounds δ)) ∧
        ((alg2Copies n ε δ * alg2Rounds δ : ℕ) : ℝ) ≤
          C * (1 / (1 - 2 * Real.sqrt ε) ^ 2) * Real.log (2 / δ) * Real.log (n / δ) := by sorry

end QuantumStateIdentity321.Schur.Supplement
