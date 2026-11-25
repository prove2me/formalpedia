-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultiDegreePositive_mixedDiff_succ_d48a8a9f08fc
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultiDegreePositive_mixedDiff_succ_d48a8a9f08fc
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:00:28.751728+00:00
-- url     : https://prove2.me/theorems/2c2f5ebd-a21c-5e1d-8eae-a17318b5830d
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Multi Degree Positive mixed Diff succ d48a8a9f08fc: P2 M Ground Theory Heights  Heights Hilbert Samuel Multi Degree Positive mixed Diff succ d48a8a9f
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Multi Degree Positive mixed Diff succ d48a8a9f08fc construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Multi Degree Positive mixed Diff succ d48a8a9f08fc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMultiDegreePositive.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMultiDegreePositive.lean#L26-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsMultiDegreePositive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSegrePrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSegreHilb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSegreDimGe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PDegreePositive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMultiDegreePositive
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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.MultiDegreePositive

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultiDegreePositive_mixedDiff_succ_d48a8a9f08fc {L : Type} [DecidableEq L] (b : L → ℤ) (H : (L → ℤ) → ℤ) (r : ℕ) :
    mixedDiff (fun _ : Fin (r + 1) => b) H = diffStep b (mixedDiff (fun _ : Fin r => b) H) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«MultiDegreePositive».«mixedDiff_succ» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultiDegreePositive_mixedDiff_succ_d48a8a9f08fc
