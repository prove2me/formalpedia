-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_wt_step
-- name    : PositivityTheory.Rg.Sw.LC.CoreC.wt_step
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:41.069322+00:00
-- url     : https://prove2.me/theorems/014d5df1-07ef-4803-9584-72add3b027fd
-- title:
--   Core C: wt step
-- statement:
--   The Core C construction uses the wt step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/CoeffSmulX.lean#L28-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/CoeffSmulX.lean#L28-L43

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BfSmulRight
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoeffSmulX
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finsupp
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreC
open PositivityTheory.Rg.Sw G
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.LC.CoreC.wt_step (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) (k : Fin m × Fin n × Bool) :
    (wt c (Finsupp.single k 1 + s) : ℂ) = ((2 * c : ℝ) : ℂ) * ((s k : ℂ) + 1) * (wt c s : ℂ) := by sorry
