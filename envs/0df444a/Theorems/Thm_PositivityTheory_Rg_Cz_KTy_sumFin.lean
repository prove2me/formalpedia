-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_KTy_sumFin
-- name    : PositivityTheory.Rg.Cz.KTy.sumFin
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:53:13.926824+00:00
-- url     : https://prove2.me/theorems/36e4f6f8-7aa3-4fbf-b947-abac0284a65f
-- title:
--   KTy: sum Fin
-- statement:
--   The KTy construction uses the sum Fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PKTypeA.lean#L126-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PKTypeA.lean#L126-L128

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
variable (nu : ι → Fin n → ℕ) (H : Finset ι)

theorem PositivityTheory.Rg.Cz.KTy.sumFin (j m : ℕ) : ∑ c : Fin j, (if (c : ℕ) = m then 1 else 0 : ℕ) = if m < j then 1 else 0 := by sorry
