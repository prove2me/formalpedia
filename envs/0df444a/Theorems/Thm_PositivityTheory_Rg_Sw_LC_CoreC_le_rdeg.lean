-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_le_rdeg
-- name    : PositivityTheory.Rg.Sw.LC.CoreC.le_rdeg
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:57:44.716433+00:00
-- url     : https://prove2.me/theorems/c641aed3-f4d0-4556-953f-fceb99c1f932
-- title:
--   Core C: le rdeg
-- statement:
--   The Core C construction uses the le rdeg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/FunctionalRepresentationByContraction.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/FunctionalRepresentationByContraction.lean#L19-L24

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_XPderivMono
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FunctionalRepresentationByContraction
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

theorem PositivityTheory.Rg.Sw.LC.CoreC.le_rdeg (ε : Fin m → Bool) (t : Fin m × Fin n × Bool →₀ ℕ) (k) (hk : inF1 ε k) : t k ≤ rdeg ε t k.1 := by sorry
