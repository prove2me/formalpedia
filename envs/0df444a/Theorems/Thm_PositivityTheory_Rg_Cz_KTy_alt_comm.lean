-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_KTy_alt_comm
-- name    : PositivityTheory.Rg.Cz.KTy.alt_comm
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:52:39.782206+00:00
-- url     : https://prove2.me/theorems/a81bc179-7313-5834-8252-b371834e9a42
-- title:
--   KTy: alt comm
-- statement:
--   The KTy construction uses the alt comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PKTypeA.lean#L201-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PKTypeA.lean#L201-L205

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

theorem PositivityTheory.Rg.Cz.KTy.alt_comm {P : Type} [Fintype P] [DecidableEq P] {M : Type} [AddCommGroup M] [Module ℂ M]
    (G : Finset (Equiv.Perm P)) (x : Module.End ℂ (TV n M P)) (h : ∀ σ ∈ G, Commute (pm σ) x) :
    Commute (alt G) x := by sorry
