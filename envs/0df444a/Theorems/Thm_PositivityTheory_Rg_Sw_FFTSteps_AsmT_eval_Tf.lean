-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_AsmT_eval_Tf
-- name    : PositivityTheory.Rg.Sw.FFTSteps.AsmT.eval_Tf
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:16:21.961387+00:00
-- url     : https://prove2.me/theorems/e385cd5a-c11a-5b1e-b9fa-af8dd71fa86d
-- title:
--   Asm T: eval Tf
-- statement:
--   The Asm T construction uses the eval Tf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/AssemblyT.lean#L82-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/AssemblyT.lean#L82-L90

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyTB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.AsmT
open AsmA
variable {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]

theorem PositivityTheory.Rg.Sw.FFTSteps.AsmT.eval_Tf (hA : Avg) (q : PV ι A B) (z : (ι × A) ⊕ (ι × B) → ℂ) :
    eval z (Tf hA q) = ∫ k : Formalism.REAL.KG (fun _ : Fin (NN ι A B) => true),
      eval (act (blk (Formalism.REAL.toMK k)) ((blk (Formalism.REAL.toMK k)).map star) z) q
        ∂(Formalism.REAL.muK (fun _ : Fin (NN ι A B) => true)) := by sorry
