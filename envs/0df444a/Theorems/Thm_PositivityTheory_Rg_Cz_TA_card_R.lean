-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TA_card_R
-- name    : PositivityTheory.Rg.Cz.TA.card_R
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:54:15.088973+00:00
-- url     : https://prove2.me/theorems/d2001d8a-3240-5c90-8c35-738036c3ce7c
-- title:
--   TA: card R
-- statement:
--   The TA construction uses the card R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransAllC.lean#L46-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransAllC.lean#L46-L59

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllC
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
  {ι : Type} [DecidableEq ι] (lab : P → ι) (τ₀ : ι)
omit [DecidableEq P]

theorem PositivityTheory.Rg.Cz.TA.card_R (τ : {τ // τ ≠ τ₀}) (co : P → Fin n) (k : Fin n) :
    (Finset.univ.filter fun p : {p // ¬ lab p = τ₀} => labR lab τ₀ p = τ ∧ co p.1 = k).card =
      (Finset.univ.filter fun p => lab p = τ.1 ∧ co p = k).card := by sorry
