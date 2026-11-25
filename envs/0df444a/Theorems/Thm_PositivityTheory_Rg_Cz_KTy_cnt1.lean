-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_KTy_cnt1
-- name    : PositivityTheory.Rg.Cz.KTy.cnt1
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:52:47.132104+00:00
-- url     : https://prove2.me/theorems/e89a394a-c6c4-5513-b487-6e8b8b5f160b
-- title:
--   KTy: cnt1
-- statement:
--   The KTy construction uses the cnt1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PKTypeA.lean#L135-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PKTypeA.lean#L135-L144

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

theorem PositivityTheory.Rg.Cz.KTy.cnt1 (τ : ι) (i : Fin n) :
    (Finset.univ.filter fun k => tl H k = τ ∧ rI H k = i).card = if τ ∈ H then (i : ℕ) else 0 := by sorry
