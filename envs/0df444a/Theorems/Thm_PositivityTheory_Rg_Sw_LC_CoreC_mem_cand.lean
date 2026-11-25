-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_mem_cand
-- name    : PositivityTheory.Rg.Sw.LC.CoreC.mem_cand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:01.210939+00:00
-- url     : https://prove2.me/theorems/c89b039a-8748-40eb-a037-5d4802c0a9f3
-- title:
--   Core C: mem cand
-- statement:
--   The Core C construction uses the mem cand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/FunctionalRepresentationByContraction.lean#L26-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/FunctionalRepresentationByContraction.lean#L26-L42

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

theorem PositivityTheory.Rg.Sw.LC.CoreC.mem_cand (ε : Fin m → Bool) (r : Fin m → ℕ) (t : Fin m × Fin n × Bool →₀ ℕ) :
    t ∈ cand ε r ↔ (∀ k ∈ t.support, inF1 ε k) ∧ rdeg ε t = r := by sorry
