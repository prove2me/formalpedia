-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_Core_pderiv_mem_supported
-- name    : PositivityTheory.Rg.Sw.LC.Core.pderiv_mem_supported
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:54:54.740741+00:00
-- url     : https://prove2.me/theorems/62fc47ac-07c2-50da-9169-bbee85e6fa4d
-- title:
--   Core: pderiv mem supported
-- statement:
--   The Core construction uses the pderiv mem supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/AdjoinFirstOperatorsPreservesFamily.lean#L19-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/AdjoinFirstOperatorsPreservesFamily.lean#L19-L35

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FformSmulRight
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_AdjoinFirstOperatorsPreservesFamily
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.Core
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.LC.Core.pderiv_mem_supported {S : Set (Fin m × Fin n × Bool)} {g : PX m n} (hg : g ∈ supported ℂ S)
    (k : Fin m × Fin n × Bool) : pderiv k g ∈ supported ℂ S := by sorry
