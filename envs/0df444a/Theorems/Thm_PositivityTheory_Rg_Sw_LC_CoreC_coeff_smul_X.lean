-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_coeff_smul_X
-- name    : PositivityTheory.Rg.Sw.LC.CoreC.coeff_smul_X
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:57:34.678862+00:00
-- url     : https://prove2.me/theorems/07e51e31-cd7f-5196-9143-df74ff6cad6b
-- title:
--   Core C: coeff smul X
-- statement:
--   The Core C construction uses the coeff smul X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/CoeffSmulX.lean#L133-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/CoeffSmulX.lean#L133-L138

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

theorem PositivityTheory.Rg.Sw.LC.CoreC.coeff_smul_X {τ : Type} [DecidableEq τ] (c : ℂ) (w0 u : τ) :
    (c • X w0 : MvPolynomial τ ℂ).coeff (Finsupp.single u 1) = if w0 = u then c else 0 := by sorry
