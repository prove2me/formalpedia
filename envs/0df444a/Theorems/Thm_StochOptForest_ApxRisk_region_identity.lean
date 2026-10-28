-- Prove2me | Theorems.Thm_StochOptForest_ApxRisk_region_identity
-- name    : StochOptForest.ApxRisk.region_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:28:54.969772+00:00
-- url     : https://prove2.me/theorems/ed4ffd1d-af42-4f20-ad5c-9345b77d2196
-- title:
--   §2.2, p. 8 — the region identity p₁f₁(z) + p₂f₂(z) = p₀f₀(z)
-- statement:
--   Let $\mu$ be the law of the features on $\mathbb R^p$ and $\bar c(x,z)$ the regression cost. Let $R_1,R_2\subseteq\mathbb R^p$ be disjoint measurable regions with $\mu(R_1)>0$ and $\mu(R_2)>0$, and let $R_0=R_1\cup R_2$. Fix $z\in\mathbb R^d$ and assume $x\mapsto\bar c(x,z)$ is integrable on $R_1$ and on $R_2$. With $p_j=\mu(R_j)$ and $f_j(z)=\mathbb E[c(z;Y)\mid X\in R_j]$,
--   $$p_1f_1(z)+p_2f_2(z)=p_0f_0(z).$$
--
--   This identity is why the first-order approximation $p_1f_1(z_0)+p_2f_2(z_0)$ of the oracle criterion does not depend on the subpartition, and why the approximate risk criterion (13) may drop these terms.
--
--   **Formalization Note** The integrability hypotheses state that the conditional expectations exist, which the paper assumes implicitly.
-- source:
--   Kallus & Mao, arXiv:2008.07473v6, p. 8, §2.2 (repeated p. 9, §2.3)

import Mathlib
import Definitions.Def_StochOptForest_ApxRisk_Model

namespace StochOptForest.ApxRisk

open MeasureTheory

theorem region_identity {p d : ℕ} (μ : Measure (Xp p)) [IsProbabilityMeasure μ]
    (cbar : Xp p → Ed d → ℝ) (R1 R2 : Set (Xp p)) (hR1 : MeasurableSet R1)
    (hR2 : MeasurableSet R2) (hdisj : Disjoint R1 R2) (hpos1 : 0 < μ R1) (hpos2 : 0 < μ R2)
    (z : Ed d) (hint1 : IntegrableOn (fun x => cbar x z) R1 μ)
    (hint2 : IntegrableOn (fun x => cbar x z) R2 μ) :
    regionProb μ R1 * regionAvg μ cbar R1 z + regionProb μ R2 * regionAvg μ cbar R2 z
      = regionProb μ (R1 ∪ R2) * regionAvg μ cbar (R1 ∪ R2) z := by sorry

end StochOptForest.ApxRisk
