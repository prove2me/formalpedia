-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_subsetDiff_eq_sum_support_020a5c302417
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_subsetDiff_eq_sum_support_020a5c302417
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:02:23.556277+00:00
-- url     : https://prove2.me/theorems/c92545da-fae8-496a-9662-a3b0d3cc19de
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman subset Diff eq sum support 020a5c302417: P2 M Ground Theory Heights  Heights Kleiman subset Diff eq sum support 020a5c302417
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman subset Diff eq sum support 020a5c302417 construction uses the P2 M Ground Theory Heights  Heights Kleiman subset Diff eq sum support 020a5c302417 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PSubsetDiffConst.lean#L36-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PSubsetDiffConst.lean#L36-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StSubsetDiffConst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PSubsetDiffConst
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
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Kleiman_subsetDiff_eq_sum_support_020a5c302417 (n : ℕ) (f : (Fin (n + 1) → ℕ) → ℤ → ℚ)
    (Q : MvPolynomial (Fin (n + 1 + 1)) ℚ)
    (hf : ∀ (x : Fin (n + 1) → ℕ) (c : ℤ),
      f x c = eval (Fin.snoc (α := fun _ => ℚ) (fun j => (x j : ℚ)) (c : ℚ)) Q)
    (m : ℕ) (c : ℤ) :
    subsetDiff n f m c = ∑ e ∈ Q.support, Q.coeff e *
      ((∏ i : Fin n, (1 - (0 : ℚ) ^ e i.castSucc.castSucc)) * (m : ℚ) ^ e (Fin.last n).castSucc *
        (c : ℚ) ^ e (Fin.last (n + 1))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«subsetDiff_eq_sum_support» := P2M_GroundTheory_Heights__Heights_Kleiman_subsetDiff_eq_sum_support_020a5c302417
