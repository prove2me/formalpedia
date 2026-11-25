-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_algebraicIndependent_rows_8439d4126368
-- name    : P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_algebraicIndependent_rows_8439d4126368
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:18:16.920314+00:00
-- url     : https://prove2.me/theorems/f1935e7a-4b44-53e7-af82-26e05064a688
-- title:
--   P2 M Ground Theory Heights  Heights Generic Linear Trdeg algebraic Independent rows 8439d4126368: P2 M Ground Theory Heights  Heights Generic Linear Trdeg algebraic Independent rows 8439d4126368
-- statement:
--   The P2 M Ground Theory Heights  Heights Generic Linear Trdeg algebraic Independent rows 8439d4126368 construction uses the P2 M Ground Theory Heights  Heights Generic Linear Trdeg algebraic Independent rows 8439d4126368 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PGenericLinearTrdeg.lean#L123-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PGenericLinearTrdeg.lean#L123-L239

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

theorem P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_algebraicIndependent_rows_8439d4126368 (F E : Type) [Field F] [Field E] [Algebra F E] (N k r : ℕ)
    (η : Fin N → E) (hrk : r ≤ k) (j : Fin r → Fin N) (hind : AlgebraicIndependent F (η ∘ j)) :
    AlgebraicIndependent F (Sum.elim (fun ij : Fin k × Fin N => (X ij : MvPolynomial (Fin k × Fin N) E))
      (fun l : Fin r => ∑ m, X (Fin.castLE hrk l, m) * C (η m))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GenericLinearTrdeg».«algebraicIndependent_rows» := P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_algebraicIndependent_rows_8439d4126368
