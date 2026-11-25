-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_det_ne
-- name    : PositivityTheory.Rg.Cz.CtrX.det_ne
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:53:56.305792+00:00
-- url     : https://prove2.me/theorems/2742d146-2cd9-4990-aee4-dfcb830aabde
-- title:
--   Ctr X: det ne
-- statement:
--   The Ctr X construction uses the det ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PContractB.lean#L42-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PContractB.lean#L42-L44

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

theorem PositivityTheory.Rg.Cz.CtrX.det_ne {ι Γ : Type} {bar : ι → ι} {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ} [Group Γ] [TopologicalSpace Γ]
    (hK : IsKD bar κ) (τ : ι) (γ : Γ) : (κ τ γ).det ≠ 0 := by sorry
