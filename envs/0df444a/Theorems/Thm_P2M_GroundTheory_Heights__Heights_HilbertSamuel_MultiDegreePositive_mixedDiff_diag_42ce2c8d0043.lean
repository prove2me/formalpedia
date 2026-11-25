-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultiDegreePositive_mixedDiff_diag_42ce2c8d0043
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultiDegreePositive_mixedDiff_diag_42ce2c8d0043
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:12:31.707332+00:00
-- url     : https://prove2.me/theorems/c58fe6ff-93fb-4574-af4c-390c31e60db9
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Multi Degree Positive mixed Diff diag 42ce2c8d0043: P2 M Ground Theory Heights  Heights Hilbert Samuel Multi Degree Positive mixed Diff diag 42ce2c8d
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Multi Degree Positive mixed Diff diag 42ce2c8d0043 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Multi Degree Positive mixed Diff diag 42ce2c8d0043 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMultiDegreePositive.lean#L30-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMultiDegreePositive.lean#L30-L40

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultiDegreePositive_mixedDiff_diag_42ce2c8d0043 {K : Type} [DecidableEq K] (h : (K → ℤ) → ℤ) (g : (Unit → ℤ) → ℤ)
    (hg : ∀ n : ℤ, g (fun _ => n) = h (fun _ => n)) (r : ℕ) (n : ℤ) :
    mixedDiff (fun _ : Fin r => fun _ : Unit => (1 : ℤ)) g (fun _ => n) =
      mixedDiff (fun _ : Fin r => fun _ : K => (1 : ℤ)) h (fun _ => n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«MultiDegreePositive».«mixedDiff_diag» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultiDegreePositive_mixedDiff_diag_42ce2c8d0043
