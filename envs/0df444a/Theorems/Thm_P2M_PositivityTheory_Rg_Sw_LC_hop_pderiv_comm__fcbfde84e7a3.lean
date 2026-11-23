-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LC_hop_pderiv_comm__fcbfde84e7a3
-- name    : P2M_PositivityTheory_Rg_Sw_LC_hop_pderiv_comm__fcbfde84e7a3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:39:05.91979+00:00
-- url     : https://prove2.me/theorems/597248c5-2cd9-4fb1-a22c-fbc83958d6c4
-- title:
--   P2 M Positivity Theory Rg Sw LC hop pderiv comm  fcbfde84e7a3: P2 M Positivity Theory Rg Sw LC hop pderiv comm  fcbfde84e7a3
-- statement:
--   The P2 M Positivity Theory Rg Sw LC hop pderiv comm  fcbfde84e7a3 construction uses the P2 M Positivity Theory Rg Sw LC hop pderiv comm  fcbfde84e7a3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/HopPderivComm.lean#L13-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/HopPderivComm.lean#L13-L21

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_HopPderivComm
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
open PositivityTheory.Rg.Sw
variable {m n : ℕ}

theorem P2M_PositivityTheory_Rg_Sw_LC_hop_pderiv_comm__fcbfde84e7a3 (i j : Fin m × Fin n × Bool) (p : PX m n) :
    pderiv (R := ℂ) i (pderiv (R := ℂ) j p) = pderiv (R := ℂ) j (pderiv (R := ℂ) i p) := by sorry

alias «PositivityTheory».«Rg».«Sw».«LC».«hop_pderiv_comm'» := P2M_PositivityTheory_Rg_Sw_LC_hop_pderiv_comm__fcbfde84e7a3
