-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TGK_actT_fin
-- name    : PositivityTheory.Rg.Cz.TGK.actT_fin
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:54:39.262827+00:00
-- url     : https://prove2.me/theorems/c73af41a-81ea-584f-af00-56b9309f988e
-- title:
--   TGK: act T fin
-- statement:
--   The TGK construction uses the act T fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKB.lean#L11-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKB.lean#L11-L30

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGKB
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.TGK
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]

theorem PositivityTheory.Rg.Cz.TGK.actT_fin {ι Γ : Type} (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M)
    (hfin : ∀ y, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun γ => ρ γ y))) (y : TV n M P) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun γ => actT lab κ ρ γ y)) := by sorry
