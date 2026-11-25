-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_KTy_half
-- name    : PositivityTheory.Rg.Cz.KTy.half
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:52:44.925533+00:00
-- url     : https://prove2.me/theorems/813228f9-c176-5c28-bc4d-e318c6d07746
-- title:
--   KTy: half
-- statement:
--   The KTy construction uses the half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PKTypeA.lean#L259-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PKTypeA.lean#L259-L264

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

theorem PositivityTheory.Rg.Cz.KTy.half (bar : ι → ι) (hinv : ∀ τ, bar (bar τ) = τ) (hne : ∀ τ, bar τ ≠ τ) :
    ∃ H : Finset ι, ∀ τ, τ ∈ H ↔ bar τ ∉ H := by sorry
