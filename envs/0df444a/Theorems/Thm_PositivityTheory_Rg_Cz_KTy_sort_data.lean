-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_KTy_sort_data
-- name    : PositivityTheory.Rg.Cz.KTy.sort_data
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:53:27.117517+00:00
-- url     : https://prove2.me/theorems/b0084dfd-0d92-477e-8ac0-ddec0a7aedcc
-- title:
--   KTy: sort data
-- statement:
--   The KTy construction uses the sort data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PKTypeA.lean#L207-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PKTypeA.lean#L207-L257

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PKTypeA
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
open PositivityTheory.Rg.Cz.KTy
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}

theorem PositivityTheory.Rg.Cz.KTy.sort_data (l : ι → Fin n → ℤ) (hl : ∀ τ, Function.Injective (l τ)) :
    ∃ (s : ℤ) (w : ι → Equiv.Perm (Fin n)) (nu : ι → Fin n → ℕ),
      (∀ τ i, (nu τ i : ℤ) = s - l τ (w τ i) - i) ∧ ∀ τ, Monotone (nu τ) := by sorry
