-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CauchyBinetMinorsAlt_principal_minor_43c2d72f49f6
-- name    : P2M_GroundTheory_Heights__Heights_CauchyBinetMinorsAlt_principal_minor_43c2d72f49f6
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:18:08.739378+00:00
-- url     : https://prove2.me/theorems/bf3c8071-e520-43ac-817e-c86c2948aa1a
-- title:
--   P2 M Ground Theory Heights  Heights Cauchy Binet Minors Alt principal minor 43c2d72f49f6: P2 M Ground Theory Heights  Heights Cauchy Binet Minors Alt principal minor 43c2d72f49f6
-- statement:
--   The P2 M Ground Theory Heights  Heights Cauchy Binet Minors Alt principal minor 43c2d72f49f6 construction uses the P2 M Ground Theory Heights  Heights Cauchy Binet Minors Alt principal minor 43c2d72f49f6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCauchyBinetMinors.lean#L61-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCauchyBinetMinors.lean#L61-L78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCauchyBinet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCauchyBinetMinors
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
open Matrix Finset
open GroundTheory.Heights₂.Heights.CauchyBinetMinorsAlt

theorem P2M_GroundTheory_Heights__Heights_CauchyBinetMinorsAlt_principal_minor_43c2d72f49f6 {p q k : ℕ} (M : Matrix (Fin p) (Fin q) ℂ)
    (S : {S : Finset (Fin q) // S.card = k}) :
    ((Mᴴ * M).submatrix (S.1.orderEmbOfFin S.2) (S.1.orderEmbOfFin S.2)).det =
      ∑ T : {T : Finset (Fin p) // T.card = k},
        ((‖(M.submatrix (T.1.orderEmbOfFin T.2) (S.1.orderEmbOfFin S.2)).det‖ ^ 2 : ℝ) : ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CauchyBinetMinorsAlt».«principal_minor» := P2M_GroundTheory_Heights__Heights_CauchyBinetMinorsAlt_principal_minor_43c2d72f49f6
