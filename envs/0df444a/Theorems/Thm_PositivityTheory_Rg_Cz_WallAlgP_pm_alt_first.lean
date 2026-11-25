-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_WallAlgP_pm_alt_first
-- name    : PositivityTheory.Rg.Cz.WallAlgP.pm_alt_first
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:49:07.594792+00:00
-- url     : https://prove2.me/theorems/9cbb7376-adf1-4d58-9ce7-74dac9e84e12
-- title:
--   Wall Alg P: pm alt first
-- statement:
--   The Wall Alg P construction uses the pm alt first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PWallAlgA.lean#L33-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PWallAlgA.lean#L33-L46

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

theorem PositivityTheory.Rg.Cz.WallAlgP.pm_alt_first {m k : ℕ} (τ : Equiv.Perm (Fin m)) (hτ : τ ∈ firstG m k) (ξ : TV n M (Fin m)) :
    pm τ (alt (firstG m k) ξ) = ((Equiv.Perm.sign τ : ℤ) : ℂ) • alt (firstG m k) ξ := by sorry
