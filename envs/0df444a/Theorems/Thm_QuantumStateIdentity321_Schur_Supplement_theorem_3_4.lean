-- Prove2me | Theorems.Thm_QuantumStateIdentity321_Schur_Supplement_theorem_3_4
-- name    : QuantumStateIdentity321.Schur.Supplement.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:54:28.825199+00:00
-- url     : https://prove2.me/theorems/1fb7e175-bff4-4390-aaee-4f097f9edfe0
-- title:
--   Theorem 3.4 — soundness of Algorithm 2, also with the soundness-only $k=\lceil8\gamma^{-2}\log(2/\delta)\rceil$
-- statement:
--   Let $n\ge3$ and $d\ge2$, let $\varepsilon\in(0,1/4)$ and $\delta\in(0,1)$, and set $\gamma=\frac12-\sqrt\varepsilon$, $\tau=(7-2\varepsilon+\sqrt\varepsilon)/8$ and $\ell=\lceil\log_3(2/\delta)\rceil$. Then:
--
--   1. Algorithm 2 with its own parameter $k=\lceil(8/\gamma^2)\log(n\ell/\delta)\rceil$ is a two-outcome measurement that rejects every no instance of $\mathrm{QSI}^\varepsilon_n$ with probability at least $1-\delta$;
--   2. for soundness alone, Algorithm 2 with the same $\tau,\ell$ and $k=\lceil(8/\gamma^2)\log(2/\delta)\rceil$ also rejects every no instance with probability at least $1-\delta$;
--   3. in both cases it consumes exactly $k\ell$ copies of each input state when $n$ is even, and, when $n$ is odd, $2k\ell$ copies of $|\psi_1\rangle$ and $k\ell$ copies of every other state;
--   4. the soundness-only number of copies is $O\bigl((1-2\sqrt\varepsilon)^{-2}\log^2(2/\delta)\bigr)$: there is an absolute constant $C$ with
--
--   $$
--   k\ell\le\frac{C}{(1-2\sqrt\varepsilon)^2}\log^2(2/\delta)\qquad\bigl(k=\lceil 8\gamma^{-2}\log(2/\delta)\rceil\bigr).
--   $$
--
--   Together with Theorem 3.5 this shows that Algorithm 2, which uses only parallel swap tests, solves $\mathrm{QSI}^\varepsilon_n$ with $O(\gamma^{-2}\log(n/\delta)\log(2/\delta))$ copies of each state.
--
--   **Formalization Note** The protocol is its accept effect (the average over the sampled matchings of the tensor product of the swap-test accept effects), and "rejects with probability at least $1-\delta$" is stated as "accepts with probability at most $\delta$". The constant $C$ is quantified before $n,d,\varepsilon,\delta$.
--
--   Differences from the source:
--   - encoding: Algorithm 2 as a procedure (sample matchings, run Algorithm 1 on every edge, reject iff a call rejects) → its accept effect alg2Effect, with validity 0 ≤ A ≤ I as a conjunct; reason: every procedure ending in accept/reject has such an effect; same algorithm
--   - reading: step 3, k = ⌈(8/γ²) log(nℓ/δ)⌉, after "n becomes even" for odd n → n is the number of input states (not the padded n + 1); reason: the procedure could be read either way; the input n gives fewer copies, the stronger claim
--   - generalization: at most 2kℓ copies of ψ₁ and kℓ of every other state when n is odd → the exact counts 2kℓ and kℓ; reason: exact counts imply the source's upper bounds
--   - encoding: O((1−2√ε)⁻² log²(2/δ)) copies → kℓ ≤ C (1−2√ε)⁻² log²(2/δ) with ∃ C > 0 before n, d, ε, δ; reason: the meaning of the O(·); it does not replace the explicit counts
--   - encoding: rejects with probability ≥ 1 − δ → accepts with probability ≤ δ; reason: the two outcome probabilities sum to 1 on unit inputs
--   - encoding: indices $1,\dots,n$ → `Fin n`, label $i$ is the source's $i+1$; reason: Lean convention; same instances
-- source:
--   Shih-Han Hung, Ming-Hsien Tsai, STOC 2027 submission #321 (October 2026), Theorem 3.4, PDF/printed p.12, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/321.pdf

import Definitions.Def_QuantumStateIdentity321_Schur_Supplement_SwapMatching

namespace QuantumStateIdentity321.Schur.Supplement

open Matrix

/-- Theorem 3.4 (soundness), p.12: for `n ≥ 3`, `d ≥ 2`, `ε ∈ (0, 1/4)` and `δ ∈ (0, 1)`, with
`τ = (7 − 2ε + √ε)/8`, `γ = 1/2 − √ε` and `ℓ = ⌈log₃(2/δ)⌉`:

1. Algorithm 2 with its own `k = ⌈(8/γ²) log(nℓ/δ)⌉` is a two-outcome measurement that rejects
   every no instance with probability at least `1 − δ`;
2. for soundness alone, `k = ⌈(8/γ²) log(2/δ)⌉` already suffices;
3. in both cases the protocol consumes exactly `kℓ` copies of each input state when `n` is even,
   and `2kℓ` copies of `|ψ₁⟩` and `kℓ` of every other state when `n` is odd;
4. the soundness-only number of copies is `O((1 − 2√ε)⁻² log²(2/δ))`: `kℓ ≤ C (1 − 2√ε)⁻² log²(2/δ)`
   for an absolute constant `C`. -/
theorem theorem_3_4 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n d : ℕ), 3 ≤ n → 2 ≤ d →
      ∀ ε δ : ℝ, 0 < ε → ε < 1 / 4 → 0 < δ → δ < 1 →
        (IsValidEffect (alg2Effect n d (alg2Rounds δ) (alg2Copies n ε δ) (swapThreshold ε)) ∧
          ∀ ψ : Fin n → State d, (∀ i, ‖ψ i‖ = 1) → IsNoInstance ε ψ →
            labelledAcceptProb
                (alg2Effect n d (alg2Rounds δ) (alg2Copies n ε δ) (swapThreshold ε))
                (alg2Label n (alg2Rounds δ) (alg2Copies n ε δ)) ψ ≤ δ) ∧
        (IsValidEffect (alg2Effect n d (alg2Rounds δ) (alg2CopiesSound ε δ) (swapThreshold ε)) ∧
          ∀ ψ : Fin n → State d, (∀ i, ‖ψ i‖ = 1) → IsNoInstance ε ψ →
            labelledAcceptProb
                (alg2Effect n d (alg2Rounds δ) (alg2CopiesSound ε δ) (swapThreshold ε))
                (alg2Label n (alg2Rounds δ) (alg2CopiesSound ε δ)) ψ ≤ δ) ∧
        (∀ i : Fin n, copyCount (alg2Label n (alg2Rounds δ) (alg2Copies n ε δ)) i =
          (if n % 2 = 1 ∧ i.val = 0 then 2 else 1) * (alg2Copies n ε δ * alg2Rounds δ)) ∧
        (∀ i : Fin n, copyCount (alg2Label n (alg2Rounds δ) (alg2CopiesSound ε δ)) i =
          (if n % 2 = 1 ∧ i.val = 0 then 2 else 1) * (alg2CopiesSound ε δ * alg2Rounds δ)) ∧
        ((alg2CopiesSound ε δ * alg2Rounds δ : ℕ) : ℝ) ≤
          C * (1 / (1 - 2 * Real.sqrt ε) ^ 2) * Real.log (2 / δ) ^ 2 := by sorry

end QuantumStateIdentity321.Schur.Supplement
