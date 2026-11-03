-- Prove2me | Theorems.Thm_ResolvingPricing_Tsharp_isStoppingTime
-- name    : ResolvingPricing.Tsharp_isStoppingTime
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:27:46.210163+00:00
-- url     : https://prove2.me/theorems/f83889bd-fa91-4376-82dc-b1519342d6cf
-- title:
--   $T^\sharp$ is a stopping time (after Eq. (8))
-- statement:
--   Let $T^\sharp$ be the time index of (8) built from the noises of a run. For every period $\tau$ the event $\{T^\sharp\ge\tau\}$ is determined by the history up to and including period $\tau$. Equivalently, in forward time, $T+1-T^\sharp$ is a stopping time of the run's filtration.
--
--   This is what allows optional stopping at $T^\sharp$ in the proofs of Lemma 2 and of (18).
--
--   **Formalization Note** The paper's $\mathcal F_\tau$ is the filtration's index $T+1-\tau$; $T^\sharp\le T+1$, so the subtraction does not truncate.
--
--   Differences from the source:
--   - generalization: T♯ built from the noises of the resolving run → T♯ built from the noises of any run, for any x and any model; reason: the claim uses only that the noises are adapted; the resolving run is one such run
--   - encoding: T♯ is a stopping time (backward time: {T♯ ≥ τ} ∈ ℱ_τ) → ω ↦ T + 1 − T♯(ω) is an ℱ-stopping time in forward time; reason: ℱ_τ (paper) is ℱ (T + 1 − τ) here and T♯ ≤ T + 1; the two statements are equivalent
--   - encoding: T♯ := max{τ ≥ 1 : |ξ̄ʳ→τ−1| > γ} ∨ ⌈2|r″(x_T)|B_ξ/r′(x_T) + 1⌉ (8) → the maximum runs over 2 ≤ τ ≤ T (empty maximum 0); ceilings are Nat.ceil; reason: τ = 1 would involve ξ̄→0, which contains ξ_1/0, and never changes T♯ because the second term is at least 1
--   - reading: A4: the conditional distribution of ξ_t given p_t is Q(p_t) → the conditional law of ξ_t given the past ℱ_{t+1} is Q(p_t) (condExp of indicators of Borel sets); reason: the Bellman equation (5) and the recursion (7), p.3543, take the expectation over ξ ~ Q(price) given the current state, and the network analogue B4 (p.3549) states independence from past noise; under the weaker reading Q does not determine R^π(T, x_T)
--   - encoding: prices p ∈ [p̲, p̄] with demand f(p) and noise law Q(p) → demand rates λ ∈ [d̲, d̄] with price g(λ) = f⁻¹(λ) and noise law Q(λ) := Q(f⁻¹(λ)); |f(p) − f(p′)| = |λ − λ′| in A5; reason: the paper's own parametrization in (5); f is a bijection [p̲, p̄] → [d̲, d̄], so the instances are the same
-- source:
--   Y. Wang, H. Wang, Constant Regret Resolving Heuristics for Price-Based Revenue Management, Oper. Res. 70(6):3538–3557 (2022), doi:10.1287/opre.2021.2219, §4.1, p.3543 (PDF p.7), after Eq. (8): "so T♯ is indeed a stopping time"

import Mathlib
import Definitions.Def_ResolvingPricing_Tsharp

open MeasureTheory

namespace ResolvingPricing

/-- **`T♯` is a stopping time**, Y. Wang, H. Wang, *Constant Regret Resolving Heuristics for Price-Based Revenue Management*,
Oper. Res. 70(6) (2022), p.3543 (after (8)): "Note that ξ̄ʳ→τ−1 is a function of
{ξʳ_t}_{t=τ}^T and is measurable with respect to ℱ_τ, so T♯ is indeed a stopping time."

In forward time `k = T − t`, the time `T + 1 − T♯` is a stopping time of the run's filtration; that is,
for every period `τ`, the event `{T♯ ≥ τ}` is known at the start of period `τ`.

**Formalization Note.** The paper's `ℱ_τ` (history through period `τ`) is `ℱ (T + 1 − τ)` here, so
`{T♯ ≥ τ} ∈ ℱ_τ` for all `τ` is the statement that `ω ↦ T + 1 − T♯(ω)` is an `ℱ`-stopping time
(`T♯ ≤ T + 1`, so the subtraction does not truncate). The paper's `T♯` is built from the resolving
run's noises; the claim uses only that the noises are adapted, so it is stated for every run, any
`x`, and any model. -/
theorem Tsharp_isStoppingTime (P : Model) (T : ℕ) (x : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (ρ : Run P T x μ ℱ) :
    IsStoppingTime ℱ (fun ω => ((T + 1 - ρ.Tsharp ω : ℕ) : WithTop ℕ)) := by sorry

end ResolvingPricing
