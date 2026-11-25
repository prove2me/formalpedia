-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_CGlue_tmap_actT
-- name    : PositivityTheory.Rg.Cz.CGlue.tmap_actT
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:48:00.095753+00:00
-- url     : https://prove2.me/theorems/6f2ac70c-7d49-5611-9434-93a0e2f48b5f
-- title:
--   CGlue: tmap act T
-- statement:
--   The CGlue construction uses the tmap act T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CoefficientGluing/SumFinVal.lean#L70-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CoefficientGluing/SumFinVal.lean#L70-L84

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_KTypeData
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CoefficientGluing_SumFinVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open Matrix Formalism.REAL
open scoped TensorProduct
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.CGlue
variable {n : ℕ} {P : Type} [Fintype P] [DecidableEq P]
variable {M : Type} [AddCommGroup M] [Module ℂ M] {d : ℕ}

theorem PositivityTheory.Rg.Cz.CGlue.tmap_actT {ι Γ : Type} (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M) (γ : Γ)
    (Jh : Matrix (Fin d) (P → Fin n) ℂ) (B : Matrix (Fin d) (Fin d) ℂ)
    (h : Jh * Matrix.of (fun I J : P → Fin n => ∏ p, κ (lab p) γ (I p) (J p)) = B * Jh) (f : TV n M P) :
    tmap Jh (actT lab κ ρ γ f) = TensorProduct.map (ρ γ) (Matrix.toLin' B) (tmap Jh f) := by sorry
