-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_AsmA_ext_all
-- name    : PositivityTheory.Rg.Sw.FFTSteps.AsmA.ext_all
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:08:45.392454+00:00
-- url     : https://prove2.me/theorems/65817c79-8e75-50c5-941c-2ca9eeb5aa26
-- title:
--   Asm A: ext all
-- statement:
--   The Asm A construction uses the ext all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/AssemblyTB.lean#L12-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/AssemblyTB.lean#L12-L47

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyTA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyTB
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.AsmA
variable {ι A B : Type} [Fintype ι] [DecidableEq ι]

theorem PositivityTheory.Rg.Sw.FFTSteps.AsmA.ext_all (hE : Ext) [Fintype A] [Fintype B] {p : PV ι A B} (hp : IsInv p) (M : Matrix ι ι ℂ)
    (z : (ι × A) ⊕ (ι × B) → ℂ) :
    eval (act M (M.map star) z) p = eval (act 1 (M.transpose * M.map star) z) p := by sorry
