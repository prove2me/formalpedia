-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_SpecA_prodL_nat
-- name    : PositivityTheory.Rg.Cz.SpecA.prodL_nat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:13:13.226858+00:00
-- url     : https://prove2.me/theorems/eab1eeab-7741-4d79-92b9-e43b6588a9fd
-- title:
--   Spec A: prod L nat
-- statement:
--   The Spec A construction uses the prod L nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PSpectrum.lean#L16-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PSpectrum.lean#L16-L31

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSpectrum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.SpecA
variable {n : ℕ}

theorem PositivityTheory.Rg.Cz.SpecA.prodL_nat {ι V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (Φ : V →ₗ[ℂ] W) (A : Module.End ℂ V) (B : Module.End ℂ W) (h : Φ ∘ₗ A = B ∘ₗ Φ) (g : ι → ℂ) (L : List ι) :
    Φ ∘ₗ (L.map fun r => A - algebraMap ℂ _ (g r)).prod = (L.map fun r => B - algebraMap ℂ _ (g r)).prod ∘ₗ Φ := by sorry
