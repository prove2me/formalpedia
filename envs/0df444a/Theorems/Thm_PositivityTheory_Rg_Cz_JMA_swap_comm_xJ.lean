-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_JMA_swap_comm_xJ
-- name    : PositivityTheory.Rg.Cz.JMA.swap_comm_xJ
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:13:19.517811+00:00
-- url     : https://prove2.me/theorems/9b23a9c5-b98c-45bb-bbd1-8d81f5ac7960
-- title:
--   JMA: swap comm x J
-- statement:
--   The JMA construction uses the swap comm x J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PJmComm.lean#L64-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PJmComm.lean#L64-L68

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PJmComm
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
open PositivityTheory.Rg.Cz.JMA
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem PositivityTheory.Rg.Cz.JMA.swap_comm_xJ (hT : TensorGl) {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) {m : ℕ} (k i j : Fin m)
    (h1 : i < k ↔ j < k) (h2 : (i = k ∨ i < k) ↔ (j = k ∨ j < k)) :
    Commute (pm (Equiv.swap i j)) (xJ E k) := by sorry
