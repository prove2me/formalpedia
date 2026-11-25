-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreD_mem_S_of
-- name    : PositivityTheory.Rg.Sw.LC.CoreD.mem_S_of
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:57:56.203587+00:00
-- url     : https://prove2.me/theorems/cfe036a3-1da3-5eed-9830-517914cb8e23
-- title:
--   Core D: mem S of
-- statement:
--   The Core D construction uses the mem S of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SymbolFirstFamilyOfMem.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SymbolFirstFamilyOfMem.lean#L33-L37

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

theorem PositivityTheory.Rg.Sw.LC.CoreD.mem_S_of {s : Sym m n} (h : SymbolInFirstFamily ε s) : s ∈ S ε s.totalDegree := by sorry
