-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_WallAlgP_om_alt
-- name    : PositivityTheory.Rg.Cz.WallAlgP.om_alt
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:48:57.264866+00:00
-- url     : https://prove2.me/theorems/7bf82a49-7ec0-43db-be78-1089ddd1d5d6
-- title:
--   Wall Alg P: om alt
-- statement:
--   The Wall Alg P construction uses the om alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PWallAlgA.lean#L244-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PWallAlgA.lean#L244-L270

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

theorem PositivityTheory.Rg.Cz.WallAlgP.om_alt {m : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (hT : ∀ (σ : Equiv.Perm (Fin m)) (p : Fin m),
      pm σ * Om E p = (Om E (σ p) * pm σ : Module.End ℂ (TV n M (Fin m)))) (k : ℕ) (ξ : TV n M (Fin m)) :
    alt (firstG m k) (∑ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k), Om E j ξ) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k), Om E j (alt (firstG m k) ξ) := by sorry
