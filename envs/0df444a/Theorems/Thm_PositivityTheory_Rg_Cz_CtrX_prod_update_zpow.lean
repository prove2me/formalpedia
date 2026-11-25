-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_prod_update_zpow
-- name    : PositivityTheory.Rg.Cz.CtrX.prod_update_zpow
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:54:45.595158+00:00
-- url     : https://prove2.me/theorems/da3f0972-fb7a-49b3-b5a4-ec0c6721c92c
-- title:
--   Ctr X: prod update zpow
-- statement:
--   The Ctr X construction uses the prod update zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PContractB.lean#L30-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PContractB.lean#L30-L40

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractD
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractE
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractB
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

theorem PositivityTheory.Rg.Cz.CtrX.prod_update_zpow {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → ℂ) (c : ι → ℤ) (τ0 : ι) (hd : d τ0 ≠ 0) :
    ∏ τ, d τ ^ (Function.update c τ0 (c τ0 - 1)) τ = (d τ0)⁻¹ * ∏ τ, d τ ^ c τ := by sorry
