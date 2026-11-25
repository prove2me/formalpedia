-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_KTy_sumRange
-- name    : PositivityTheory.Rg.Cz.KTy.sumRange
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:53:20.728314+00:00
-- url     : https://prove2.me/theorems/c7b12a8c-c334-4059-bcfe-176dba78e01b
-- title:
--   KTy: sum Range
-- statement:
--   The KTy construction uses the sum Range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PKTypeA.lean#L130-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PKTypeA.lean#L130-L133

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

theorem PositivityTheory.Rg.Cz.KTy.sumRange (n m : ℕ) : ∑ j ∈ Finset.range n, (if m < j then 1 else 0 : ℕ) = n - (m + 1) := by sorry
