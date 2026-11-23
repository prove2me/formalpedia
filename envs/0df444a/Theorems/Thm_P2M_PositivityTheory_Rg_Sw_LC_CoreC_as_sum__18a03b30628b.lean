-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LC_CoreC_as_sum__18a03b30628b
-- name    : P2M_PositivityTheory_Rg_Sw_LC_CoreC_as_sum__18a03b30628b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:53.810054+00:00
-- url     : https://prove2.me/theorems/21fcb37a-a363-448a-89c2-f99dc9740532
-- title:
--   P2 M Positivity Theory Rg Sw LC Core C as sum  18a03b30628b: P2 M Positivity Theory Rg Sw LC Core C as sum  18a03b30628b
-- statement:
--   The P2 M Positivity Theory Rg Sw LC Core C as sum  18a03b30628b construction uses the P2 M Positivity Theory Rg Sw LC Core C as sum  18a03b30628b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/FunctionalRepresentationByContraction.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/FunctionalRepresentationByContraction.lean#L57-L60

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

theorem P2M_PositivityTheory_Rg_Sw_LC_CoreC_as_sum__18a03b30628b (p : PX m n) : p = ∑ s ∈ p.support, p.coeff s • monomial s (1 : ℂ) := by sorry

alias «PositivityTheory».«Rg».«Sw».«LC».«CoreC».«as_sum'» := P2M_PositivityTheory_Rg_Sw_LC_CoreC_as_sum__18a03b30628b
