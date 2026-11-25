-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_KTy_cnt2
-- name    : PositivityTheory.Rg.Cz.KTy.cnt2
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:53:09.355751+00:00
-- url     : https://prove2.me/theorems/1a1b71e1-cd31-5edf-abfa-40299793e2ba
-- title:
--   KTy: cnt2
-- statement:
--   The KTy construction uses the cnt2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PKTypeA.lean#L146-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PKTypeA.lean#L146-L169

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

theorem PositivityTheory.Rg.Cz.KTy.cnt2 (bar : ι → ι) (hinv : ∀ τ, bar (bar τ) = τ) (τ : ι) (i : Fin n) :
    (Finset.univ.filter fun k => bar (tl H k) = τ ∧ Fin.rev (cI H k) = i).card = if bar τ ∈ H then (i : ℕ) else 0 := by sorry
