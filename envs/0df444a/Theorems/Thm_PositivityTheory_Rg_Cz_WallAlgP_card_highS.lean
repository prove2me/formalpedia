-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_WallAlgP_card_highS
-- name    : PositivityTheory.Rg.Cz.WallAlgP.card_highS
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:49:51.88403+00:00
-- url     : https://prove2.me/theorems/39b96395-64d9-4822-9173-7005328f566d
-- title:
--   Wall Alg P: card high S
-- statement:
--   The Wall Alg P construction uses the card high S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PWallAlgA.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PWallAlgA.lean#L17-L23

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PWallAlgA
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
open PositivityTheory.Rg.Cz.WallAlgP
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem PositivityTheory.Rg.Cz.WallAlgP.card_highS {m k : ℕ} (hk : k ≤ m) :
    (Finset.univ.filter fun j : Fin m => k ≤ (j : ℕ)).card = m - k := by sorry
