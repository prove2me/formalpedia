-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TGK_pm_actT
-- name    : PositivityTheory.Rg.Cz.TGK.pm_actT
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:53:56.570858+00:00
-- url     : https://prove2.me/theorems/09605425-5fe2-4df9-8443-eb642f3c0c43
-- title:
--   TGK: pm act T
-- statement:
--   The TGK construction uses the pm act T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKA.lean#L224-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKA.lean#L224-L228

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGKA
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

theorem PositivityTheory.Rg.Cz.TGK.pm_actT {ι Γ : Type} (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M)
    (σ : Equiv.Perm P) (hσ : ∀ p, lab (σ p) = lab p) (γ : Γ) : Commute (pm σ) (actT lab κ ρ γ) := by sorry
