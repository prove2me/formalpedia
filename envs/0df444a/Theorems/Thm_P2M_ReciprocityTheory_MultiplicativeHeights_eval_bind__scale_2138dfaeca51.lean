-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_MultiplicativeHeights_eval_bind__scale_2138dfaeca51
-- name    : P2M_ReciprocityTheory_MultiplicativeHeights_eval_bind__scale_2138dfaeca51
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:17:42.370811+00:00
-- url     : https://prove2.me/theorems/834624cb-c297-40a2-a9ef-63fe278323dc
-- title:
--   P2 M Reciprocity Theory Multiplicative Heights eval bind  scale 2138dfaeca51: P2 M Reciprocity Theory Multiplicative Heights eval bind  scale 2138dfaeca51
-- statement:
--   The P2 M Reciprocity Theory Multiplicative Heights eval bind  scale 2138dfaeca51 construction uses the P2 M Reciprocity Theory Multiplicative Heights eval bind  scale 2138dfaeca51 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SphereTorusB.lean#L33-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SphereTorusB.lean#L33-L40

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereTorusA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereTorusB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory

theorem P2M_ReciprocityTheory_MultiplicativeHeights_eval_bind__scale_2138dfaeca51 {ι : Type*} (r w : ι → ℂ) (f : MvPolynomial ι ℂ) :
    MvPolynomial.eval w
        (MvPolynomial.bind₁ (fun j => MvPolynomial.C (r j) * MvPolynomial.X j) f) =
      MvPolynomial.eval (fun j => r j * w j) f := by sorry

alias «ReciprocityTheory».«MultiplicativeHeights».«eval_bind₁_scale» := P2M_ReciprocityTheory_MultiplicativeHeights_eval_bind__scale_2138dfaeca51
