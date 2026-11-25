-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_AsmT_integrable_eval_act
-- name    : PositivityTheory.Rg.Sw.FFTSteps.AsmT.integrable_eval_act
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:15:17.131392+00:00
-- url     : https://prove2.me/theorems/ddc6d131-1753-43c3-ba3d-10ad41ab465d
-- title:
--   Asm T: integrable eval act
-- statement:
--   The Asm T construction uses the integrable eval act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/AssemblyT.lean#L118-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/AssemblyT.lean#L118-L121

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

theorem PositivityTheory.Rg.Sw.FFTSteps.AsmT.integrable_eval_act (hA : Avg) (F G : Formalism.REAL.KG (fun _ : Fin (NN ι A B) => true) → Matrix ι ι ℂ)
    (hF : Continuous F) (hG : Continuous G) (z : (ι × A) ⊕ (ι × B) → ℂ) (q : PV ι A B) :
    Integrable (fun k => eval (act (F k) (G k) z) q) (Formalism.REAL.muK (fun _ : Fin (NN ι A B) => true)) := by sorry
