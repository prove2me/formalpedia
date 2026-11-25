-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_contr_eq_bf
-- name    : PositivityTheory.Rg.Sw.LC.CoreC.contr_eq_bf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:26.710906+00:00
-- url     : https://prove2.me/theorems/69a17d80-f484-4801-918b-74b1b4c95d13
-- title:
--   Core C: contr eq bf
-- statement:
--   The Core C construction uses the contr eq bf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PartialDerivZeroSecondFamily.lean#L189-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PartialDerivZeroSecondFamily.lean#L189-L196

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoeffSmulX
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PartialDerivZeroSecondFamily
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

theorem PositivityTheory.Rg.Sw.LC.CoreC.contr_eq_bf (ε : Fin m → Bool) (c : ℝ) {h g : PX m n} (hh : h ∈ F1 ε) (hg : g ∈ F2 ε) :
    contr c (h * g) = bf (fun s => (wt c s : ℂ)) h (rename pE g) := by sorry
