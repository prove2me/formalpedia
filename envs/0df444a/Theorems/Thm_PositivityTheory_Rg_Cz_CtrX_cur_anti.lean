-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_cur_anti
-- name    : PositivityTheory.Rg.Cz.CtrX.cur_anti
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:53:54.530683+00:00
-- url     : https://prove2.me/theorems/49e7e752-d571-5859-b570-845012ebd2a9
-- title:
--   Ctr X: cur anti
-- statement:
--   The Ctr X construction uses the cur anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PContractA.lean#L104-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PContractA.lean#L104-L132

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

theorem PositivityTheory.Rg.Cz.CtrX.cur_anti {m : ℕ} (h : n ≤ m) (η : TV n M (Fin m))
    (hη : ∀ τ ∈ firstG m n, pm τ η = ((Equiv.Perm.sign τ : ℤ) : ℂ) • η) (σ : Equiv.Perm (Fin n)) :
    pm σ (cur (reIx (splitE m n h) η)) = ((Equiv.Perm.sign σ : ℤ) : ℂ) • cur (reIx (splitE m n h) η) := by sorry
