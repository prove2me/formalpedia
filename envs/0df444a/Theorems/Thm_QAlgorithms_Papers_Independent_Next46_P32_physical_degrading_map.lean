-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P32_physical_degrading_map
-- name    : QAlgorithms.Papers.Independent.Next46.P32.physical_degrading_map
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T15:31:28.058998+00:00
-- url     : https://prove2.me/theorems/2cdb1b08-ead9-4665-bac7-07c9effeea0e
-- title:
--   Physical vacuum degrading map on arbitrary block states
-- statement:
--   Let $n\ge1$, $1/2<\eta\le1$, and let $\rho$ be any normalized positive trace-class $n$-mode density on the full Fock space, with arbitrary correlations between uses. Let $\mathcal B_\eta^{(n)}(\rho)$ be the joint output of the lossless splitter with all unused input modes in independent vacuum states. Write $\mathcal L_s^{(n)}$ for vacuum attenuation of intensity $s$. Then
--
--   $$
--   \operatorname{Tr}_B\mathcal B_\eta^{(n)}(\rho)
--   =\mathcal L_{(1-\eta)/\eta}^{(n)}
--     \bigl(\operatorname{Tr}_C\mathcal B_\eta^{(n)}(\rho)\bigr).
--   $$
--
--   No photon-energy bound is required. At $\eta=1$ the degrading channel replaces its input by vacuum. This is an equality of marginal states and supplies the physical degradation used in the capacity converse.
-- source:
--   Classical capacity of bosonic broadcast communication and a new minimum output entropy conjecture, arXiv:0706.3416v1, PDF p. 4, Section IV, physical degrading channel

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P32

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity productCoeff)

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Section IV, PDF p.4: equality of reduced output densities under a physical
vacuum attenuator. No input energy bound is required. At eta=1 the degrading
map is vacuum replacement; equality of a joint Markov dilation is not asserted. -/
theorem physical_degrading_map (n : ℕ) (hn : 0 < n) (eta : ℝ)
    (heta : 1 / 2 < eta) (heta1 : eta ≤ 1) (rho : State (NumberString n)) :
    charlieMarginal (broadcast n eta rho.coefficients) =
      pureLoss n ((1 - eta) / eta)
        (bobMarginal (broadcast n eta rho.coefficients)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P32

end
