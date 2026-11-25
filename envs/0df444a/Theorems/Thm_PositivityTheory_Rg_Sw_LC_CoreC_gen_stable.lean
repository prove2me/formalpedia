-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_gen_stable
-- name    : PositivityTheory.Rg.Sw.LC.CoreC.gen_stable
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:57:26.421812+00:00
-- url     : https://prove2.me/theorems/650abfe6-b17a-5bbe-89b2-d9cb6ce471e9
-- title:
--   Core C: gen stable
-- statement:
--   The Core C construction uses the gen stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/CoeffSmulX.lean#L91-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/CoeffSmulX.lean#L91-L98

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

theorem PositivityTheory.Rg.Sw.LC.CoreC.gen_stable (ε : Fin m → Bool) (i j : Fin n) (R : Set (Fin m → ℕ)) (s : Fin m × Fin n × Bool →₀ ℕ)
    (hs : ∀ k ∈ s.support, inF1 ε k) (hR : rdeg ε s ∈ R) : KopL ε i j (monomial s (1 : ℂ)) ∈ box ε R := by sorry
