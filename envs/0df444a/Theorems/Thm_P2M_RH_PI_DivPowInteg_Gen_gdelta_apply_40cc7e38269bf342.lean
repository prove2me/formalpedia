-- Prove2me | Theorems.Thm_P2M_RH_PI_DivPowInteg_Gen_gdelta_apply_40cc7e38269bf342
-- name    : P2M_RH_PI_DivPowInteg_Gen_gdelta_apply_40cc7e38269bf342
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:37:04.960514+00:00
-- url     : https://prove2.me/theorems/7d15929b-e46a-4bb5-9c44-e8790b77e7d8
-- title:
--   P2 M RH PI Div Pow Integ Gen gdelta apply 40cc7e38269bf342: P2 M RH PI Div Pow Integ Gen gdelta apply 40cc7e38269bf342
-- statement:
--   The P2 M RH PI Div Pow Integ Gen gdelta apply 40cc7e38269bf342 construction uses the P2 M RH PI Div Pow Integ Gen gdelta apply 40cc7e38269bf342 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/DividedPowerIntegrals/GenVan.lean#L82-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/DividedPowerIntegrals/GenVan.lean#L82-L84

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenVan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.DivPowInteg PI.DivPowInteg.Gen
variable {K I J : Type} [CommRing K] [Fintype I] [Fintype J]

theorem P2M_RH_PI_DivPowInteg_Gen_gdelta_apply_40cc7e38269bf342 (κ : I → J → K) (R : MvPolynomial (I ⊕ J) K) :
    gdelta κ R = ∑ i, ∑ j, κ i j • pderiv (Sum.inl i) (pderiv (Sum.inr j) R) := by sorry

alias «PI».«DivPowInteg».«Gen».«gdelta_apply» := P2M_RH_PI_DivPowInteg_Gen_gdelta_apply_40cc7e38269bf342
