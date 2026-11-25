-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_exists_indep_0c0d576242a7
-- name    : P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_exists_indep_0c0d576242a7
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:18:22.482862+00:00
-- url     : https://prove2.me/theorems/bc53a83e-8d62-5441-8280-3d6b6fc99383
-- title:
--   P2 M Ground Theory Heights  Heights Generic Linear Trdeg exists indep 0c0d576242a7: P2 M Ground Theory Heights  Heights Generic Linear Trdeg exists indep 0c0d576242a7
-- statement:
--   The P2 M Ground Theory Heights  Heights Generic Linear Trdeg exists indep 0c0d576242a7 construction uses the P2 M Ground Theory Heights  Heights Generic Linear Trdeg exists indep 0c0d576242a7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PGenericLinearTrdeg.lean#L241-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PGenericLinearTrdeg.lean#L241-L273

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PGenericLinearTrdeg
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
open MvPolynomial
open GroundTheory.Heights₂.Heights.GenericLinearTrdeg

theorem P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_exists_indep_0c0d576242a7 {F E : Type} [Field F] [Field E] [Algebra F E] {N : ℕ} (η : Fin N → E) (d : ℕ)
    (hd : Algebra.trdeg F (Algebra.adjoin F (Set.range η)) = d) :
    ∃ j : Fin d → Fin N, AlgebraicIndependent F (η ∘ j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GenericLinearTrdeg».«exists_indep» := P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_exists_indep_0c0d576242a7
