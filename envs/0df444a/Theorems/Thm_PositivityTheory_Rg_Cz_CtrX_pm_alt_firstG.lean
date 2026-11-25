-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_pm_alt_firstG
-- name    : PositivityTheory.Rg.Cz.CtrX.pm_alt_firstG
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:53:49.055803+00:00
-- url     : https://prove2.me/theorems/82a186a8-241f-4921-9b1b-4ec17ce37130
-- title:
--   Ctr X: pm alt first G
-- statement:
--   The Ctr X construction uses the pm alt first G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PContractA.lean#L72-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PContractA.lean#L72-L102

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractA
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.CtrX
open PositivityTheory.Rg.Cz
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem PositivityTheory.Rg.Cz.CtrX.pm_alt_firstG {m k : ℕ} (τ : Equiv.Perm (Fin m)) (hτ : τ ∈ firstG m k) (x : TV n M (Fin m)) :
    pm τ (alt (firstG m k) x) = ((Equiv.Perm.sign τ : ℤ) : ℂ) • alt (firstG m k) x := by sorry
