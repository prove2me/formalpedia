-- Prove2me | Theorems.Thm_ProperHalfspace_proposition_16
-- name    : ProperHalfspace.proposition_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:04:07.420122+00:00
-- url     : https://prove2.me/theorems/305cf5b4-6028-4df0-871e-1b0bd76412b7
-- title:
--   Proposition 16 — the membership-query matrix estimator (corrected: $n\ge1$)
-- statement:
--   There is one program and a universal constant $C$ such that the following holds for all $n\ge1$, $f:\{\pm1\}^n\to[-1,1]$, $\rho\in(0,1)$ and $\beta,\kappa,\delta\in(0,1/2)$, with $\eta=\min\{\kappa,\delta\}$.
--
--   1. On every coin tape, the program halts with a positive semidefinite matrix $\hat M$ with $\mathrm{Tr}(\hat M)\le1$, after at most $Cn\eta^{-2}\log(1/\beta)$ queries and at most $C(n^2\eta^{-2}\log(1/\beta)+n^2\log^2(1/\beta)+n^3)$ units of work.
--   2. With probability at least $1-\beta$,
--   $$\|\hat M-M_\rho(f)\|_{\mathrm{op}}\le\kappa,\qquad\max_i|\hat M_{ii}-M_\rho(f)_{ii}|\le\delta.$$
--
--   The constant does not depend on $(1-\rho)^{-1}$. This is how the learner accesses the influence PCA matrix.
--
--   Differences from the source:
--   - correction: every n, with query and time bounds that vanish at n = 0 → n ≥ 1; reason: at n = 0 the time bound is 0, but a halting run takes at least one step
--   - reading: the real-RAM model, with no instruction set named (p.2) → the local machine ProperHalfspace.Machine, with exact + − × ÷, rational literals, fair coins, query at cost n, and no √, floor, eigensolver or uniform real draw; reason: the page names no instructions; every primitive added would weaken the theorem
--   - reading: "the construction uses N = O(η⁻²) independent restrictions and two independent batches of R = n uniform points per restriction" → not stated; its observable content is the query bound at fixed β; reason: a sentence about the construction, which an input-output statement over programs cannot name
--   - encoding: O(·) → one constant C chosen before all the data; reason: the page's constants are universal (p.10)
--   - encoding: probability over the algorithm's coins → a count over coin tapes of length the work bound, rounded up; reason: a run within B units of work reads at most B coins
-- source:
--   De, Mossel, Nadimpalli, Neeman, Efficient Proper Agnostic Learning of Halfspaces, arXiv:2611.02344 (Nov. 1, 2026), Proposition 16, p.21; proof, App. B, pp.45–47

import Mathlib
import Definitions.Def_ProperHalfspace_Machine
import Definitions.Def_ProperHalfspace_InfluencePCA
import Definitions.Def_ProperHalfspace_TopEigenspace

namespace ProperHalfspace

/-- Proposition 16, p.21 (membership-query matrix estimator). De, Mossel, Nadimpalli, Neeman, arXiv:2611.02344 (Nov. 1, 2026). One
program on the real RAM with one universal `C`, for all `n ≥ 1`, `f : {±1}ⁿ → [−1, 1]`, `ρ ∈ (0, 1)`, `β, κ, δ ∈ (0, 1/2)` and
`η = min{κ, δ}`. On every tape it halts with `M̂` positive semidefinite and `Tr M̂ ≤ 1`, after at most `C n η⁻² log(1/β)` queries and
`C (n² η⁻² log(1/β) + n² log²(1/β) + n³)` work. With probability at least `1 − β`, `‖M̂ − M_ρ(f)‖_op ≤ κ` and
`maxᵢ |M̂_ii − M_ρ(f)_ii| ≤ δ`.

**Formalization Note.** `C` comes before `ρ`, which is the page's "no additional dependence on `(1−ρ)⁻¹`". `‖·‖_op` is the `ℓ₂` operator
norm. The probability is the count over tapes of length the work bound (rounded up), which no run reads past. -/
theorem proposition_16 : ∃ P : Program, Admissible P ∧ ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n →
    ∀ ρ β κ δ : ℝ, 0 < ρ → ρ < 1 → 0 < β → β < 1 / 2 → 0 < κ → κ < 1 / 2 → 0 < δ → δ < 1 / 2 →
    ∀ f : Cube n → ℝ, IsBoundedOne f →
      let η : ℝ := min κ δ
      let W : ℝ := (C : ℝ) * ((n : ℝ) ^ 2 * η⁻¹ ^ 2 * Real.log (1 / β) +
        (n : ℝ) ^ 2 * Real.log (1 / β) ^ 2 + (n : ℝ) ^ 3)
      (∀ tape : ℕ → Bool, ∃ t : ℕ,
        let s := run P f tape (estimatorInit n ρ β κ δ) t
        s.halted = true ∧ (decodeMatrix n s).PosSemidef ∧ (decodeMatrix n s).trace ≤ 1 ∧
        (s.queries : ℝ) ≤ (C : ℝ) * (n : ℝ) * η⁻¹ ^ 2 * Real.log (1 / β) ∧ (s.work : ℝ) ≤ W) ∧
      1 - β ≤ tapeProb ⌈W⌉₊ (fun tape => ∃ t : ℕ,
        let s := run P f tape (estimatorInit n ρ β κ δ) t
        s.halted = true ∧ opNorm (decodeMatrix n s - pcaMatrix ρ f) ≤ κ ∧
        ∀ i, |decodeMatrix n s i i - pcaMatrix ρ f i i| ≤ δ) := by sorry

end ProperHalfspace
