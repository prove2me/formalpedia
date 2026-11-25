-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TGK_tE_comm
-- name    : PositivityTheory.Rg.Cz.TGK.tE_comm
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:54:15.457176+00:00
-- url     : https://prove2.me/theorems/dc9450ed-9c9e-4658-b3a4-77e642f02679
-- title:
--   TGK: t E comm
-- statement:
--   The TGK construction uses the t E comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKA.lean#L157-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKA.lean#L157-L168

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGKA
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.TGK
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]

theorem PositivityTheory.Rg.Cz.TGK.tE_comm {ι : Type} [DecidableEq ι] (E : ι → Fin n → Fin n → Module.End ℂ M)
    (hcomm : ∀ τ τ', τ ≠ τ' → ∀ a b c d, Commute (E τ a b) (E τ' c d)) (lab : P → ι) (τ τ' : ι) (h : τ ≠ τ')
    (a b c d : Fin n) : Commute (tE (fib lab τ) (E τ) a b) (tE (fib lab τ') (E τ') c d) := by sorry
