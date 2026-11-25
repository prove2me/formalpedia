-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitCurve_isMultiHomogIdeal_orbitIdeal_5ad0b5ef0050
-- name    : P2M_GroundTheory_Heights__Heights_OrbitCurve_isMultiHomogIdeal_orbitIdeal_5ad0b5ef0050
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:03:18.985407+00:00
-- url     : https://prove2.me/theorems/a718c07b-f88f-5007-befc-9e935b0154c5
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Curve is Multi Homog Ideal orbit Ideal 5ad0b5ef0050: P2 M Ground Theory Heights  Heights Orbit Curve is Multi Homog Ideal orbit Ideal 5ad0b5ef0050
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Curve is Multi Homog Ideal orbit Ideal 5ad0b5ef0050 construction uses the P2 M Ground Theory Heights  Heights Orbit Curve is Multi Homog Ideal orbit Ideal 5ad0b5ef0050 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCurve.lean#L71-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCurve.lean#L71-L80

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCurve
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G Algebra
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitCurve
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_OrbitCurve_isMultiHomogIdeal_orbitIdeal_5ad0b5ef0050 (x : Cone n (AlgebraicClosure ℚ)) :
    Geo.IsMultiHomogIdeal (ι := blockIdx n) (orbitIdeal x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitCurve».«isMultiHomogIdeal_orbitIdeal» := P2M_GroundTheory_Heights__Heights_OrbitCurve_isMultiHomogIdeal_orbitIdeal_5ad0b5ef0050
