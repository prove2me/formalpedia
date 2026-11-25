-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TF_qdet_mem
-- name    : PositivityTheory.Rg.Cz.TF.qdet_mem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:55:52.983099+00:00
-- url     : https://prove2.me/theorems/c2bddb1f-489c-501b-ac61-f318ee267ce0
-- title:
--   TF: qdet mem
-- statement:
--   The TF construction uses the qdet mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransFinA.lean#L40-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransFinA.lean#L40-L52

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFinCK
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFinA
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.TF

theorem PositivityTheory.Rg.Cz.TF.qdet_mem {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A) (B : Subalgebra ℂ A)
    (hF : ∀ a b, F a b ∈ B) (u : ℂ) : qdet F u ∈ B := by sorry
