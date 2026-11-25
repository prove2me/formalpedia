-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_InterNumEventual_mixed_eval_ec46f79ca513
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_InterNumEventual_mixed_eval_ec46f79ca513
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:31:04.753699+00:00
-- url     : https://prove2.me/theorems/37ce4e85-8ca8-5f28-9947-5662ce838d57
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Inter Num Eventual mixed eval ec46f79ca513: P2 M Ground Theory Heights  Heights Kleiman Inter Num Eventual mixed eval ec46f79ca513
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Inter Num Eventual mixed eval ec46f79ca513 construction uses the P2 M Ground Theory Heights  Heights Kleiman Inter Num Eventual mixed eval ec46f79ca513 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumEventual.lean#L36-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumEventual.lean#L36-L61

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumEventual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PRestrLenEuler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperDiffPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PInterNumEventual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.InterNumEventual

theorem P2M_GroundTheory_Heights__Heights_Kleiman_InterNumEventual_mixed_eval_ec46f79ca513 {n : ℕ} (Q : MvPolynomial (Fin (n + 1)) ℚ) (hQ : Q.totalDegree ≤ n) (c : ℚ) :
    ∑ T : Finset (Fin n), (-1 : ℚ) ^ (n - T.card) *
        eval (Fin.snoc (α := fun _ => ℚ) (fun j => ((ind T j : ℕ) : ℚ)) c) Q =
      ∑ d ∈ Q.support, Q.coeff d * ∏ i : Fin n, (1 - (0 : ℚ) ^ d i.castSucc) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«InterNumEventual».«mixed_eval» := P2M_GroundTheory_Heights__Heights_Kleiman_InterNumEventual_mixed_eval_ec46f79ca513
