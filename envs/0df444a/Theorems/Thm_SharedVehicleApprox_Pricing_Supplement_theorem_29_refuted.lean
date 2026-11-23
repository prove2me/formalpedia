-- Prove2me | Theorems.Thm_SharedVehicleApprox_Pricing_Supplement_theorem_29_refuted
-- name    : SharedVehicleApprox.Pricing.Supplement.theorem_29_refuted
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:44:09.209974+00:00
-- url     : https://prove2.me/theorems/55ee6ce9-88aa-43ed-b0bd-95120e92d462
-- title:
--   Theorem 29 (corrected: refutation of the printed discrete-grid guarantee) — one-station revenue counterexample
-- statement:
--   Theorem 29 is false as printed. Take one station, one unit, arrival rate one, uniform values on $[0,1]$, revenue $R(q)=q(1-q)$, and available quantiles $3/5$ and $1/10$ in decreasing order. The unrestricted optimum is $q'=1/2$ and Algorithm 7 rounds it to $\tilde q=1/10$. The printed condition holds for $\alpha=1$, since $3/5\ge1/10$. Yet
--
--   $$\alpha\mathrm{Obj}_1(\tilde q)=9/100<6/25=\mathrm{Opt}_1,$$
--
--   and $m/(m+n-1)=1$. The Lean statement includes concavity, demand connectivity, Algorithm 6 optimality, Algorithm 7 maximal rounding, normalized stationary laws, grid membership of the competing policy and the exact discrete optimum against every admissible policy and law. It states the refutation, rather than silently changing the grid inequality or adding coverage assumptions.
--
--   Differences from the source:
--   - correction: the printed condition α qᵢˢ ≥ qᵢˢ⁺¹ implies the Algorithm 7 approximation bound → an explicit counterexample satisfying the printed grid condition with α = 1 and violating the bound; reason: n = m = 1, φ = 1, uniform values and revenue R(q) = q(1−q); grid (3/5, 1/10), unrestricted optimum 1/2, rounded output 1/10. Its value 9/100 is below the discrete optimum 6/25. The claim is false with all source assumptions satisfied; no unsubstantiated repair of the grid condition is imposed
--   - encoding: optimal state-dependent discrete point prices and Algorithm 7 rounding → IsAlg6Optimal, IsAlg7Output using IsGreatest, and a bound on every discrete point policy and stationary law; reason: at one station and one unit there is a single state; its normalized law has mass one and all policies reduce to a choice from the grid
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, p. 37 (PDF 38), Theorem 29

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_PointPricing
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_DiscretePointPricing

open Finset QueueingFundamentals.Networks

namespace SharedVehicleApprox.Pricing.Supplement

/-- Refutation of Theorem 29, p. 37: one station, one unit, uniform values, revenue,
grid `(3/5, 1/10)` and `α = 1`. The printed adjacent-grid condition holds, but
Algorithm 7 rounds the unrestricted optimum `1/2` to `1/10`, earning `9/100`
instead of the discrete optimum `6/25` at `3/5`. -/
theorem theorem_29_refuted :
    let φ : Fin 1 → Fin 1 → ℝ := fun _ _ => 1
    let I : Fin 1 → Fin 1 → ℝ → ℝ := fun _ _ q => 1 - q
    let grid : Fin 1 → Finset ℝ := fun _ => {3 / 5, 1 / 10}
    let levels : Fin 2 → ℝ := ![3 / 5, 1 / 10]
    let q' : Fin 1 → ℝ := fun _ => 1 / 2
    let qt : Fin 1 → ℝ := fun _ => 1 / 10
    let qc : Fin 1 → ℝ := fun _ => 3 / 5
    let π : (Fin 1 → ℕ) → ℝ := fun x => if x ∈ states 1 1 then 1 else 0
    (∀ i j, 0 ≤ φ i j) ∧ SupportConnected φ (fun _ _ => 1) ∧
    (∀ i j, ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (rewardCurve I i j)) ∧
    (∀ i, ∀ v ∈ grid i, 0 ≤ v ∧ v ≤ 1) ∧
    Antitone levels ∧ (1 : ℝ) * levels 0 ≥ levels 1 ∧
    IsAlg6Optimal φ I q' ∧ IsAlg7Output grid q' qt ∧
    IsDiscretePointPolicy 1 1 grid (fun x i => toPolicy (pointQuantile qc) x i 0) ∧
    IsStationary 1 1 φ (toPolicy (pointQuantile qt)) π ∧
    IsStationary 1 1 φ (toPolicy (pointQuantile qc)) π ∧
    obj 1 1 φ I (toPolicy (pointQuantile qt)) π = 9 / 100 ∧
    obj 1 1 φ I (toPolicy (pointQuantile qc)) π = 6 / 25 ∧
    (∀ (q : (Fin 1 → ℕ) → Fin 1 → ℝ) (πc : (Fin 1 → ℕ) → ℝ),
      IsDiscretePointPolicy 1 1 grid q → IsStationary 1 1 φ (pointPolicy q) πc →
        obj 1 1 φ I (pointPolicy q) πc ≤ 6 / 25) ∧
    ¬ ((1 : ℝ) * obj 1 1 φ I (toPolicy (pointQuantile qt)) π ≥
      (1 : ℝ) / (1 + 1 - 1) * (6 / 25)) := by sorry

end SharedVehicleApprox.Pricing.Supplement
