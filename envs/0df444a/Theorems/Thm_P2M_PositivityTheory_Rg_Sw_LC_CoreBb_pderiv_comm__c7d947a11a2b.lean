-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LC_CoreBb_pderiv_comm__c7d947a11a2b
-- name    : P2M_PositivityTheory_Rg_Sw_LC_CoreBb_pderiv_comm__c7d947a11a2b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:26.493516+00:00
-- url     : https://prove2.me/theorems/bdc44d95-25e4-4aa7-81cf-693ba84758db
-- title:
--   P2 M Positivity Theory Rg Sw LC Core Bb pderiv comm  c7d947a11a2b: P2 M Positivity Theory Rg Sw LC Core Bb pderiv comm  c7d947a11a2b
-- statement:
--   The P2 M Positivity Theory Rg Sw LC Core Bb pderiv comm  c7d947a11a2b construction uses the P2 M Positivity Theory Rg Sw LC Core Bb pderiv comm  c7d947a11a2b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ProdMapPowSingle.lean#L13-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ProdMapPowSingle.lean#L13-L24

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.CoreBb
open PositivityTheory.Rg.Sw
variable {m n : ℕ}

theorem P2M_PositivityTheory_Rg_Sw_LC_CoreBb_pderiv_comm__c7d947a11a2b {σ : Type*} (i j : σ) (f : MvPolynomial σ ℂ) :
    pderiv i (pderiv j f) = pderiv j (pderiv i f) := by sorry

alias «PositivityTheory».«Rg».«Sw».«LC».«CoreBb».«pderiv_comm'» := P2M_PositivityTheory_Rg_Sw_LC_CoreBb_pderiv_comm__c7d947a11a2b
