-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_term_mem_box
-- name    : PositivityTheory.Rg.Sw.LC.CoreC.term_mem_box
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:57:16.926795+00:00
-- url     : https://prove2.me/theorems/59d6b049-feb4-4f6e-bc77-d6e06e72aea6
-- title:
--   Core C: term mem box
-- statement:
--   The Core C construction uses the term mem box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/CoeffSmulX.lean#L71-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/CoeffSmulX.lean#L71-L89

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

theorem PositivityTheory.Rg.Sw.LC.CoreC.term_mem_box (ε : Fin m → Bool) (R : Set (Fin m → ℕ)) (k l : Fin m × Fin n × Bool)
    (hk : inF1 ε k) (hl : inF1 ε l) (hkl : k.1 = l.1) (s : Fin m × Fin n × Bool →₀ ℕ)
    (hs : ∀ k ∈ s.support, inF1 ε k) (hR : rdeg ε s ∈ R) :
    X k * pderiv l (monomial s (1 : ℂ)) ∈ box ε R := by sorry
