-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreD_rr_aeval
-- name    : PositivityTheory.Rg.Sw.LC.CoreD.rr_aeval
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:26:15.476576+00:00
-- url     : https://prove2.me/theorems/5b65de71-bf6f-434f-ab4c-1a2b106f2efd
-- title:
--   Core D: rr aeval
-- statement:
--   The Core D construction uses the rr aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/BoxLeFirstFamily.lean#L98-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/BoxLeFirstFamily.lean#L98-L108

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymKEqZeroOfOm
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BoxLeFirstFamily
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreD
variable {m n : ℕ} {ε : Fin m → Bool}
variable (R : Set (Fin m → ℕ)) (hV : ∀ (i j : Fin n), ∀ f ∈ box ε R, KopL ε i j f ∈ box ε R)
variable (hS : SymKComm)
include hS

theorem PositivityTheory.Rg.Sw.LC.CoreD.rr_aeval (N : ℕ) (q : Polynomial ℂ) (x : S (n := n) ε N) :
    rr R N (Polynomial.aeval (OmS ε N) q x) = Polynomial.aeval (OmH R hV) q (rr R N x) := by sorry
