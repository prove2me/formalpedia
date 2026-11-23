-- Prove2me | Theorems.Thm_P2M_RH_PI_WickFormula_Gen_gdelta_apply_432825626bc43230
-- name    : P2M_RH_PI_WickFormula_Gen_gdelta_apply_432825626bc43230
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:10.980131+00:00
-- url     : https://prove2.me/theorems/1b0e2708-0481-4027-9cbd-a21f8f078ee3
-- title:
--   P2 M RH PI Wick Formula Gen gdelta apply 432825626bc43230: P2 M RH PI Wick Formula Gen gdelta apply 432825626bc43230
-- statement:
--   The P2 M RH PI Wick Formula Gen gdelta apply 432825626bc43230 construction uses the P2 M RH PI Wick Formula Gen gdelta apply 432825626bc43230 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/GenVan.lean#L85-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/GenVan.lean#L85-L88

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_GenDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_GenVan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.WickFormula PI.WickFormula.Gen
variable {K I J : Type} [CommRing K] [Fintype I] [Fintype J]

theorem P2M_RH_PI_WickFormula_Gen_gdelta_apply_432825626bc43230 (κ : I → J → K) (R : MvPolynomial (I ⊕ J) K) :
    gdelta κ R = ∑ i, ∑ j, κ i j • pderiv (Sum.inl i) (pderiv (Sum.inr j) R) := by sorry

alias «PI».«WickFormula».«Gen».«gdelta_apply» := P2M_RH_PI_WickFormula_Gen_gdelta_apply_432825626bc43230
