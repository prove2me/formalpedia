-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LC_Core_monomial_mem_supported__ab1f28bee6a5
-- name    : P2M_PositivityTheory_Rg_Sw_LC_Core_monomial_mem_supported__ab1f28bee6a5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:39:17.197818+00:00
-- url     : https://prove2.me/theorems/09f713f0-9943-4cf3-ad0c-2fe33c6ed524
-- title:
--   P2 M Positivity Theory Rg Sw LC Core monomial mem supported  ab1f28bee6a5: P2 M Positivity Theory Rg Sw LC Core monomial mem supported  ab1f28bee6a5
-- statement:
--   The P2 M Positivity Theory Rg Sw LC Core monomial mem supported  ab1f28bee6a5 construction uses the P2 M Positivity Theory Rg Sw LC Core monomial mem supported  ab1f28bee6a5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/MonomialMemSupported.lean#L13-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/MonomialMemSupported.lean#L13-L19

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_AdjoinFirstOperatorsPreservesFamily
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MonomialMemSupported
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

theorem P2M_PositivityTheory_Rg_Sw_LC_Core_monomial_mem_supported__ab1f28bee6a5 {S : Set (Fin m × Fin n × Bool)} (s : Fin m × Fin n × Bool →₀ ℕ)
    (hs : ∀ k ∈ s.support, k ∈ S) (a : ℂ) : (monomial s a : PX m n) ∈ supported ℂ S := by sorry

alias «PositivityTheory».«Rg».«Sw».«LC».«Core».«monomial_mem_supported'» := P2M_PositivityTheory_Rg_Sw_LC_Core_monomial_mem_supported__ab1f28bee6a5
