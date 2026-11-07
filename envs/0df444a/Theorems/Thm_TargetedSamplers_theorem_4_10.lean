-- Prove2me | Theorems.Thm_TargetedSamplers_theorem_4_10
-- name    : TargetedSamplers.theorem_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:12:18.278351+00:00
-- url     : https://prove2.me/theorems/7df8f1a2-b414-4ffd-991e-d8ee180ccbd8
-- title:
--   Theorem 4.10 — the Dvir–Wigderson merger and its batch time (corrected: batch time for constant γ)
-- statement:
--   For every real $\lambda>0$ and every $\gamma=\gamma(n)>0$ there is a family of $[\rho\mapsto(1-\lambda)\rho]^{\ell:1}_{\sim\gamma(n)}$-mergers
--   $$M_{\mathrm{DW}}:(\{0,1\}^n)^\ell\times\{0,1\}^d\to\{0,1\}^n,\qquad d=\lceil\lambda^{-1}\log_2(2\ell/\gamma(n))\rceil,$$
--   one for every $n$, $\ell$ and every $\rho\in[0,1]$. If $\gamma$ is a constant, one program computes the outputs of the merger on all seeds (as a multiset), for $\ell\ge1$, in time
--   $$T_{\mathrm{batch\text{-}DW}}(n,\ell)=\tilde O(\ell^3+n\,\ell^{1+1/\lambda}).$$
--
--   The merger turns the somewhere-condenser into a seeded condenser with a short seed (Theorem 4.14).
--
--   Differences from the source:
--   - correction: time clause for γ = γ(n) > 0 → time clause only when γ is constant; reason: counterexample: for γ(n) = 2^{−n}, ℓ = 1, there are 2^d ≥ 2^{n/λ} seeds and the n-bit outputs alone exceed Õ(1 + n); the page calls γ a constant and Theorem C.3 keeps it constant
--   - reading: an explicit merger (output length unspecified), ρ unrestricted → output length n, every n and every ρ ∈ [0,1], d = ⌈λ⁻¹log(2ℓ/γ)⌉; reason: as restated in Theorem C.3; an unspecified output length would allow m = 0, which is trivially a merger
--   - encoding: the multiset of outputs on all seeds → the program prints the outputs in some order whose multiset is that multiset; reason: a multiset has no order
--   - encoding: ℓ unrestricted → the time clause is for ℓ ≥ 1; reason: at ℓ = 0 the input is the empty string for every n, so one program cannot print the n-bit output; the merger of Theorem C.3 has ℓ ≥ 1 sources
--   - reading: "runs in time t" on an unspecified RAM → time at most budget = K·(t+1)·(log₂(n+t+2)+1)^k on the log-cost RAM; reason: the paper fixes no cost model; the log-cost RAM differs from a word RAM by polylogarithmic factors
--   - reading: γ-close: "L1 norm (i.e. statistical distance)" → statistical distance ½‖P−Q‖₁ ≤ γ; reason: the page equates the two; statistical distance is the standard notion for condensers
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Theorem 4.10, p.22 (pdf p.24); Theorem C.3, p.97 (pdf p.99)

import Mathlib
import Definitions.Def_TargetedSamplers_IsMerger
import Definitions.Def_TargetedSamplers_Machine
import Definitions.Def_TargetedSamplers_encInput

namespace TargetedSamplers

/-- Theorem 4.10 ([DW08; DKS+13]) (Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027
submission, manuscript sha256 599d0a59…, p.22; restated as Theorem C.3, p.97). For every real
`λ > 0` and `γ = γ(n) > 0` there is an explicit `[ρ ↦ (1 − λ)ρ]^{ℓ:1}_{∼γ}`-merger
`M_DW : ({0,1}ⁿ)^ℓ × {0,1}^d → {0,1}ⁿ`, for every `n`, `ℓ` and `ρ ∈ [0,1]`, with seed length
`d = ⌈λ^{−1} log(2ℓ/γ)⌉`; for constant `γ`, the outputs of the merger on all seeds are computable in
time `T_batch-DW(n, ℓ) = Õ(ℓ³ + n ℓ^{1+1/λ})`.

**Formalization Note** The output length `n` and the ceiling in `d` are those of Theorem C.3. The
time clause is stated for constant `γ`, as "real constants λ > 0 and γ" and Theorem C.3 ("for
simplicity we keep it a constant") say: for subconstant `γ` it is false, since the `2^d ≥ (2ℓ/γ)^{1/λ}`
outputs of `n` bits already exceed the bound (e.g. `γ(n) = 2^{−n}`, `ℓ = 1`). `Õ` is `budget`; the
`ℓ` inputs are given as one string (`encInput`), and the outputs are written in some order (a
multiset). The time clause is for `ℓ ≥ 1`: with `ℓ = 0` the input is empty and does not determine
`n`. -/
theorem theorem_4_10 (lam : ℝ) (hlam : 0 < lam) (γ : ℕ → ℝ) (hγ : ∀ n, 0 < γ n) :
    ∃ (d : ℕ → ℕ → ℕ)
      (M : (n ℓ : ℕ) → (Fin ℓ → Fin n → Bool) → (Fin (d n ℓ) → Bool) → Fin n → Bool),
      (∀ n ℓ, d n ℓ = ⌈lam⁻¹ * Real.logb 2 (2 * ℓ / γ n)⌉₊) ∧
      (∀ (n ℓ : ℕ) (ρ : ℝ), 0 ≤ ρ → ρ ≤ 1 → IsMerger ρ ((1 - lam) * ρ) (γ n) (M n ℓ)) ∧
      ((∃ γ₀ : ℝ, ∀ n, γ n = γ₀) →
        ∃ (P : Program) (K k : ℕ), ∀ (n ℓ : ℕ), 1 ≤ ℓ → ∀ xs : Fin ℓ → Fin n → Bool,
          P.OutputsMultisetIn
            (Tapes.ofInput (encInput [] (List.ofFn fun i => List.ofFn (xs i))))
            (budget K k (ℓ ^ 3 + n * ⌈(ℓ : ℝ) ^ (1 + 1 / lam)⌉₊) (n * ℓ))
            (Finset.univ.val.map fun s => List.ofFn (M n ℓ xs s))) := by sorry

end TargetedSamplers
