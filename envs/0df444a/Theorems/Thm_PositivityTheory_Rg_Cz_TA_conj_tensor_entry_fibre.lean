-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TA_conj_tensor_entry_fibre
-- name    : PositivityTheory.Rg.Cz.TA.conj_tensor_entry_fibre
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:53:51.092275+00:00
-- url     : https://prove2.me/theorems/60cdc731-754e-49c8-a250-6ad8a1eaa70e
-- title:
--   TA: conj tensor entry fibre
-- statement:
--   The TA construction uses the conj tensor entry fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransAllC.lean#L28-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransAllC.lean#L28-L43

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

theorem PositivityTheory.Rg.Cz.TA.conj_tensor_entry_fibre (τ : {τ // τ ≠ τ₀}) (F : Fin n → Fin n → Module.End ℂ M) (c d : Fin n) :
    cj (spl (n := n) (M := M) fun p => lab p = τ₀) (lift (tE (fib (labR lab τ₀) τ) F c d)) =
      tE (fib lab τ.1) F c d := by sorry
