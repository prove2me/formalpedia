-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ConeComplexBaseChange_map_int_complex_eq_43e09671a890
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ConeComplexBaseChange_map_int_complex_eq_43e09671a890
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:11.520396+00:00
-- url     : https://prove2.me/theorems/5a38b81e-1a72-41e9-9564-6636df496543
-- title:
--   P2 M Ground Theory Heights  Heights Targets Cone Complex Base Change map int complex eq 43e09671a890: P2 M Ground Theory Heights  Heights Targets Cone Complex Base Change map int complex eq 43e09671a8
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Cone Complex Base Change map int complex eq 43e09671a890 construction uses the P2 M Ground Theory Heights  Heights Targets Cone Complex Base Change map int complex eq 43e09671a890 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PConeComplexBaseChange.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PConeComplexBaseChange.lean#L19-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsConeComplexBaseChange
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PConeComplexBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.Targets.ConeComplexBaseChange
variable {σ : Type} [Fintype σ]
omit [Fintype σ]

theorem P2M_GroundTheory_Heights__Heights_Targets_ConeComplexBaseChange_map_int_complex_eq_43e09671a890 :
    (MvPolynomial.map (Int.castRingHom ℂ) : MvPolynomial σ ℤ →+* MvPolynomial σ ℂ) =
      (MvPolynomial.map (algebraMap ℚ ℂ)).comp (MvPolynomial.map (Int.castRingHom ℚ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ConeComplexBaseChange».«map_int_complex_eq» := P2M_GroundTheory_Heights__Heights_Targets_ConeComplexBaseChange_map_int_complex_eq_43e09671a890
