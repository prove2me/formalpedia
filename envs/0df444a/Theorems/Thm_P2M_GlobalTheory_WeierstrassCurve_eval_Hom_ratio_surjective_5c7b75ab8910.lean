-- Prove2me | Theorems.Thm_P2M_GlobalTheory_WeierstrassCurve_eval_Hom_ratio_surjective_5c7b75ab8910
-- name    : P2M_GlobalTheory_WeierstrassCurve_eval_Hom_ratio_surjective_5c7b75ab8910
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:55:29.240803+00:00
-- url     : https://prove2.me/theorems/d32df649-5caf-4861-972b-07d89c626f8f
-- title:
--   P2 M Global Theory Weierstrass Curve eval Hom ratio surjective 5c7b75ab8910: P2 M Global Theory Weierstrass Curve eval Hom ratio surjective 5c7b75ab8910
-- statement:
--   The P2 M Global Theory Weierstrass Curve eval Hom ratio surjective 5c7b75ab8910 construction uses the P2 M Global Theory Weierstrass Curve eval Hom ratio surjective 5c7b75ab8910 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/SpecMapAwayFnEquivAwayChart.lean#L130-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/SpecMapAwayFnEquivAwayChart.lean#L130-L146

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AwayToSectionFromZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineHomOfIsPullbackSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_SpecMapAwayFnEquivAwayChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap resG constFn)
open GlobalTheory.ProjFrac GlobalTheory.QCoh.Qcqs GlobalTheory.TangentOrigin
open GlobalTheory
open GlobalTheory.WeierstrassCurve
variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

theorem P2M_GlobalTheory_WeierstrassCurve_eval_Hom_ratio_surjective_5c7b75ab8910 (i : Fin 3) :
    Function.Surjective (MvPolynomial.eval₂Hom (constOn W (coordOpen W i)) (ratio W i)) := by sorry

alias «GlobalTheory».«WeierstrassCurve».«eval₂Hom_ratio_surjective» := P2M_GlobalTheory_WeierstrassCurve_eval_Hom_ratio_surjective_5c7b75ab8910
