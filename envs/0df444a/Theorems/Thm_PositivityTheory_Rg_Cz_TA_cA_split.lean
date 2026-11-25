-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TA_cA_split
-- name    : PositivityTheory.Rg.Cz.TA.cA_split
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:53:33.825743+00:00
-- url     : https://prove2.me/theorems/79390bbd-d05e-5ca8-be67-d5d34cbd9473
-- title:
--   TA: c A split
-- statement:
--   The TA construction uses the c A split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransAllB.lean#L110-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransAllB.lean#L110-L157

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.TA
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
  (q : P → Prop) [DecidablePred q]

theorem PositivityTheory.Rg.Cz.TA.cA_split {C : Type} [DecidableEq C] (col : P → C) (hq : ∀ p p', col p = col p' → (q p ↔ q p'))
    (b : P → Fin n) (F : TV n M P) :
    cA col b F = cA (fun x : {p // ¬ q p} => col x.1) (fun x => b x.1)
      (cA (fun x : {p // q p} => col x.1) (fun x => b x.1) (spl q F)) := by sorry
