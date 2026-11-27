-- Prove2me | Theorems.Thm_TwoSidedMatching_Statics_Supplement_theorem_4
-- name    : TwoSidedMatching.Statics.Supplement.theorem_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T22:06:10.887705+00:00
-- url     : https://prove2.me/theorems/b4f27210-1427-49a2-88f0-a70315db321c
-- title:
--   Theorem 4 — all uniform dispersion comparisons, exact thresholds and zero widths
-- statement:
--   Let buyer values be uniform on $[V-d,V+d]$ and seller costs uniform on $[C-s,C+s]$, where $C<V$ and $d,s\ge0$, with $\lambda^dT=\lambda^sT=1$. Prices and volume are selected by the uniform quantile optimization, and profit is its independently defined optimum. Set
--
--   $$k(x)=\max\{((V-C)/3-x)^+,(\sqrt{(V-C)x}-x)^+\}.$$
--
--   With the other width fixed, $p^*$ decreases on $d\in[0,k(s)]$ and increases on $d\ge k(s)$; it increases with $s$. Symmetrically, $w^*$ increases on $s\in[0,k(d)]$ and decreases on $s\ge k(d)$; it decreases with $d$. The volume $\mu^*$ decreases when the total width increases. Profit decreases for total width in $[0,V-C]$ and increases for total width at least $V-C$. All monotonicities are weak, and comparisons of total widths allow either decomposition into $d,s$.
--
--   The optimizer and value are attained, and
--
--   $$\mu^*=\begin{cases}1,&d+s=0,\\ \min\{(1+(V-C)/(d+s))/4,1\},&d+s>0.\end{cases}$$
--
--   If $d+s\le(V-C)/3$, then $p^*=V-d$, $w^*=C+s$ and $\bar J^*=V-C-d-s$. On the common positive-width domain $C-s\ge0$, all four objects agree with the published Statics construction for any rates and horizon with both expected arrival counts equal to one. **Formalization Note** The compatibility restriction applies only to this concluding bridge, not to any dispersion comparison. No density continuity or positivity of the widths is required by the main result.
--
--   Differences from the source:
--   - reading: Theorem 4 permits all nonnegative widths while its density notation degenerates at zero width → optimize the uniform quantile objective for every pair of nonnegative widths, with mu=1 at total width zero; reason: the low-width branch in Supplemental Note pp. 16–17 determines that boundary value
--   - reading: the uniform proof uses unrestricted quantile prices while program (D) restricts prices to nonnegative values → state all uniform quantile comparisons on the full printed width domain and conclude agreement with (D) when both widths are positive and C-s is nonnegative; reason: this preserves the source-supported uniform reading without claiming signed-price trajectories are feasible in (D)
--   - encoding: the proof identifies the optimizing quantiles and low-width branch → include optimizer/value attainment, the closed-form volume and the low-width identities as conclusions alongside all seven comparative-statistics assertions; reason: these conclusions verify the optimization interpretation and its zero-width boundary rather than assuming the comparative statics
-- source:
--   Chen and Hu, Pricing and Matching with Forward-looking Buyers and Sellers, submitted manuscript (SSRN 2859864, TSpace copy), Online Appendix p. 5, Theorem 4; Supplemental Note pp. 16–17, proof of Theorem 4

import Mathlib
import Definitions.Def_TwoSidedMatching_Statics_Supplement_Uniform

namespace TwoSidedMatching.Statics.Supplement

/-- All clauses of Theorem 4, with the quantile optimization and its representation bridge. -/
theorem theorem_4 (V C : ℝ) (hCV : C < V) :
    (∀ s : ℝ, 0 ≤ s →
      AntitoneOn (fun d => uniformP V C d s) (Set.Icc 0 (turn V C s)) ∧
      MonotoneOn (fun d => uniformP V C d s) (Set.Ici (turn V C s))) ∧
    (∀ d : ℝ, 0 ≤ d → MonotoneOn (fun s => uniformP V C d s) (Set.Ici 0)) ∧
    (∀ d : ℝ, 0 ≤ d →
      MonotoneOn (fun s => uniformW V C d s) (Set.Icc 0 (turn V C d)) ∧
      AntitoneOn (fun s => uniformW V C d s) (Set.Ici (turn V C d))) ∧
    (∀ s : ℝ, 0 ≤ s → AntitoneOn (fun d => uniformW V C d s) (Set.Ici 0)) ∧
    (∀ d₁ s₁ d₂ s₂ : ℝ, 0 ≤ d₁ → 0 ≤ s₁ → 0 ≤ d₂ → 0 ≤ s₂ →
      d₁ + s₁ ≤ d₂ + s₂ → uniformMu V C d₂ s₂ ≤ uniformMu V C d₁ s₁) ∧
    (∀ d₁ s₁ d₂ s₂ : ℝ, 0 ≤ d₁ → 0 ≤ s₁ → 0 ≤ d₂ → 0 ≤ s₂ →
      d₁ + s₁ ≤ d₂ + s₂ → d₂ + s₂ ≤ V - C →
      uniformValue V C d₂ s₂ ≤ uniformValue V C d₁ s₁) ∧
    (∀ d₁ s₁ d₂ s₂ : ℝ, 0 ≤ d₁ → 0 ≤ s₁ → 0 ≤ d₂ → 0 ≤ s₂ →
      V - C ≤ d₁ + s₁ → d₁ + s₁ ≤ d₂ + s₂ →
      uniformValue V C d₁ s₁ ≤ uniformValue V C d₂ s₂) ∧
    (∀ d s : ℝ, 0 ≤ d → 0 ≤ s →
      IsGreatest (uniformOptimizers V C d s) (uniformMu V C d s) ∧
      IsGreatest (uniformObjective V C d s '' Set.Icc 0 1) (uniformValue V C d s) ∧
      uniformMu V C d s =
        (if d + s = 0 then 1 else min ((1 + (V - C) / (d + s)) / 4) 1) ∧
      (d + s ≤ (V - C) / 3 →
        uniformMu V C d s = 1 ∧ uniformP V C d s = V - d ∧
        uniformW V C d s = C + s ∧ uniformValue V C d s = V - C - d - s)) ∧
    (∀ (E : TwoSidedMatching.Statics.Environment) (d s lamD lamS T : ℝ),
      0 < d → 0 < s → 0 ≤ C - s → IsUniformMarket E V C d s →
      0 < T → lamD * T = 1 → lamS * T = 1 →
      TwoSidedMatching.Statics.muStar E lamD lamS T = uniformMu V C d s ∧
      TwoSidedMatching.Statics.pStar E lamD lamS T = uniformP V C d s ∧
      TwoSidedMatching.Statics.wStar E lamD lamS T = uniformW V C d s ∧
      TwoSidedMatching.Statics.fluidValue E lamD lamS T = uniformValue V C d s) := by sorry

end TwoSidedMatching.Statics.Supplement
