-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_mhNeg_939cfeec3808
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_mhNeg_939cfeec3808
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:23:35.758091+00:00
-- url     : https://prove2.me/theorems/d40b668b-0e79-4a7a-84db-6661b8bbb69f
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line mh Neg 939cfeec3808: P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line mh Neg 939cfeec3808
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line mh Neg 939cfeec3808 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line mh Neg 939cfeec3808 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ArithModel.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ArithModel.lean#L32-L35

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsSmoothPts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_mhNeg_939cfeec3808 {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (-f) a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ProjLine».«mhNeg» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_mhNeg_939cfeec3808
