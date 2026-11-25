-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PowSpanB_natCast_smul_add_mem_W
-- name    : PositivityTheory.Rg.Sw.FFTSteps.PowSpanB.natCast_smul_add_mem_W
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:55:00.621194+00:00
-- url     : https://prove2.me/theorems/dafa208e-26c2-4ae3-97de-a44ea3a0317b
-- title:
--   Pow Span B: nat Cast smul add mem W
-- statement:
--   The Pow Span B construction uses the nat Cast smul add mem W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/PowSpan.lean#L42-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/PowSpan.lean#L42-L48

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_PowSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps
open PositivityTheory.Rg.Sw.FFTSteps.PowSpanB
variable {m n : ℕ} (ε : Fin m → Bool)

theorem PositivityTheory.Rg.Sw.FFTSteps.PowSpanB.natCast_smul_add_mem_W {w v : PX m n} (hw : w ∈ W ε) (hv : v ∈ W ε) (t : ℕ) : (t : ℂ) • v + w ∈ W ε := by sorry
