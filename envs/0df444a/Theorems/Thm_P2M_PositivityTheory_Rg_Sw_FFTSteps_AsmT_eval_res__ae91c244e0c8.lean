-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_FFTSteps_AsmT_eval_res__ae91c244e0c8
-- name    : P2M_PositivityTheory_Rg_Sw_FFTSteps_AsmT_eval_res__ae91c244e0c8
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:14:48.55981+00:00
-- url     : https://prove2.me/theorems/f327470c-e340-4e9d-ba53-0e98fc958d0a
-- title:
--   P2 M Positivity Theory Rg Sw FFTSteps Asm T eval res  ae91c244e0c8: P2 M Positivity Theory Rg Sw FFTSteps Asm T eval res  ae91c244e0c8
-- statement:
--   The P2 M Positivity Theory Rg Sw FFTSteps Asm T eval res  ae91c244e0c8 construction uses the P2 M Positivity Theory Rg Sw FFTSteps Asm T eval res  ae91c244e0c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/AssemblyT.lean#L58-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/AssemblyT.lean#L58-L61

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

theorem P2M_PositivityTheory_Rg_Sw_FFTSteps_AsmT_eval_res__ae91c244e0c8 (z : (ι × A) ⊕ (ι × B) → ℂ) (v : (Fin (NN ι A B) × A) ⊕ (Fin (NN ι A B) × B)) :
    eval z (resφ ι v) = Sum.elim (fun x : Fin (NN ι A B) × A => (invE A B x.1).elim 0 fun i => z (Sum.inl (i, x.2)))
      (fun y : Fin (NN ι A B) × B => (invE A B y.1).elim 0 fun i => z (Sum.inr (i, y.2))) v := by sorry

alias «PositivityTheory».«Rg».«Sw».«FFTSteps».«AsmT».«eval_resφ» := P2M_PositivityTheory_Rg_Sw_FFTSteps_AsmT_eval_res__ae91c244e0c8
