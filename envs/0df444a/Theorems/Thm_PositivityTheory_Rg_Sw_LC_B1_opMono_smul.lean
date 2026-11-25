-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_opMono_smul
-- name    : PositivityTheory.Rg.Sw.LC.B1.opMono_smul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:54:02.511523+00:00
-- url     : https://prove2.me/theorems/2d9036e0-9b01-540a-a13b-d4e46f9778c8
-- title:
--   B1: op Mono smul
-- statement:
--   The B1 construction uses the op Mono smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PderivPowMonomial.lean#L71-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PderivPowMonomial.lean#L71-L72

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivPowMonomial
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.B1
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
local notation "σ" => Fin m × Fin n × Bool

theorem PositivityTheory.Rg.Sw.LC.B1.opMono_smul (t : σ ⊕ σ →₀ ℕ) (c : ℂ) (f : PX m n) : opMono t (c • f) = c • opMono t f := by sorry
