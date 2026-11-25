-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_LieInverse_Sop_single
-- name    : PositivityTheory.Rg.Cz.LieInverse.Sop_single
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:53:07.882792+00:00
-- url     : https://prove2.me/theorems/08ab9dde-835a-4d45-8ebc-84b576cc2aad
-- title:
--   Lie Inverse: Sop single
-- statement:
--   The Lie Inverse construction uses the Sop single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PLieInv.lean#L58-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PLieInv.lean#L58-L68

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PLieInv
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
open PositivityTheory.Rg.Cz.LieInverse

theorem PositivityTheory.Rg.Cz.LieInverse.Sop_single {ι : Type} {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
    (E : ι → Fin n → Fin n → Module.End ℂ M) (bar : ι → ι) (τ : ι) (p q : Fin n) (z : ℂ) :
    Sop E bar τ (Matrix.single p q z) = z • E τ p q + star z • E (bar τ) p q := by sorry
