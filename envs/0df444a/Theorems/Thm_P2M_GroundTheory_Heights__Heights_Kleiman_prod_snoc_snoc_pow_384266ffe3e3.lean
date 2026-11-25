-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_prod_snoc_snoc_pow_384266ffe3e3
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_prod_snoc_snoc_pow_384266ffe3e3
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:07:04.527415+00:00
-- url     : https://prove2.me/theorems/7c7ef919-0d50-528d-9af1-b8ef3f233f2b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman prod snoc snoc pow 384266ffe3e3: P2 M Ground Theory Heights  Heights Kleiman prod snoc snoc pow 384266ffe3e3
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman prod snoc snoc pow 384266ffe3e3 construction uses the P2 M Ground Theory Heights  Heights Kleiman prod snoc snoc pow 384266ffe3e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PSubsetDiffConst.lean#L24-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PSubsetDiffConst.lean#L24-L34

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_prod_snoc_snoc_pow_384266ffe3e3 (n : ℕ) (T : Finset (Fin n)) (m : ℕ) (c : ℤ) (e : Fin (n + 1 + 1) → ℕ) :
    ∏ j, (Fin.snoc (α := fun _ => ℚ)
        (fun j => ((Fin.snoc (α := fun _ => ℕ) (fun i => if i ∈ T then 1 else 0) m j : ℕ) : ℚ))
        (c : ℚ) j) ^ e j =
      (∏ i : Fin n, (if i ∈ T then (1 : ℚ) else 0) ^ e i.castSucc.castSucc) *
        (m : ℚ) ^ e (Fin.last n).castSucc * (c : ℚ) ^ e (Fin.last (n + 1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«prod_snoc_snoc_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_prod_snoc_snoc_pow_384266ffe3e3
