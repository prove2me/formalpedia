-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreD_monomial_mem_S
-- name    : PositivityTheory.Rg.Sw.LC.CoreD.monomial_mem_S
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:57:36.610587+00:00
-- url     : https://prove2.me/theorems/bb0e9202-ae4e-49be-aa98-a1b645d3df58
-- title:
--   Core D: monomial mem S
-- statement:
--   The Core D construction uses the monomial mem S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SymbolFirstFamilyOfMem.lean#L67-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SymbolFirstFamilyOfMem.lean#L67-L71

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_EquivLift
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ZeroRight
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymbolFirstFamilyOfMem
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
variable {m n : ℕ} (ε : Fin m → Bool)
variable {ε}

theorem PositivityTheory.Rg.Sw.LC.CoreD.monomial_mem_S {N : ℕ} {u} (hu : u ∈ U ε N) (r : ℂ) : monomial u r ∈ S (n := n) ε N := by sorry
