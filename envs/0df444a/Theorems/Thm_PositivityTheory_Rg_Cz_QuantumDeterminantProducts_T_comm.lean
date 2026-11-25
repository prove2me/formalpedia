-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_QuantumDeterminantProducts_T_comm
-- name    : PositivityTheory.Rg.Cz.QuantumDeterminantProducts.T_comm
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:48:15.967605+00:00
-- url     : https://prove2.me/theorems/968c35da-0832-4ac2-8997-40babc98b005
-- title:
--   Quantum Determinant Products: T comm
-- statement:
--   The Quantum Determinant Products construction uses the T comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PPiQdet.lean#L93-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PPiQdet.lean#L93-L98

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PPiQdet
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
open PositivityTheory.Rg.Cz.QuantumDeterminantProducts
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem PositivityTheory.Rg.Cz.QuantumDeterminantProducts.T_comm (hT : TensorGl) (E : Fin n → Fin n → Module.End ℂ M) (hE : GlRel E) (u : ℂ) (σ : Equiv.Perm (Fin n))
    (j : Fin n) (hj : σ j = j) : Commute (pm σ) (T E u j) := by sorry
