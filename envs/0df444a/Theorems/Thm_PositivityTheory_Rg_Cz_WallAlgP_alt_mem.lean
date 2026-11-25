-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_WallAlgP_alt_mem
-- name    : PositivityTheory.Rg.Cz.WallAlgP.alt_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:49:20.364488+00:00
-- url     : https://prove2.me/theorems/d48d39b3-65fa-4d88-bb19-6b96697d4336
-- title:
--   Wall Alg P: alt mem
-- statement:
--   The Wall Alg P construction uses the alt mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PWallAlgA.lean#L55-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PWallAlgA.lean#L55-L59

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

theorem PositivityTheory.Rg.Cz.WallAlgP.alt_mem {m k : ℕ} (X : Submodule ℂ (TV n M (Fin m))) (hP : ∀ σ, ∀ ξ ∈ X, pm σ ξ ∈ X) (ξ) (hξ : ξ ∈ X) :
    alt (firstG m k) ξ ∈ X := by sorry
