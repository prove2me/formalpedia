-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_KTy_cntF
-- name    : PositivityTheory.Rg.Cz.KTy.cntF
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:53:22.338338+00:00
-- url     : https://prove2.me/theorems/e86d7d66-22c0-4ae6-af9f-89d8a15fe61c
-- title:
--   KTy: cnt F
-- statement:
--   The KTy construction uses the cnt F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PKTypeA.lean#L171-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PKTypeA.lean#L171-L182

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

theorem PositivityTheory.Rg.Cz.KTy.cntF (bar : ι → ι) (hinv : ∀ τ, bar (bar τ) = τ) (hH : ∀ τ, τ ∈ H ↔ bar τ ∉ H) (τ : ι) (i : Fin n) :
    (Finset.univ.filter fun p => lab3 bar (labQ nu) (tl H) p = τ ∧ bF nu H p = i).card = nu τ i + i := by sorry
