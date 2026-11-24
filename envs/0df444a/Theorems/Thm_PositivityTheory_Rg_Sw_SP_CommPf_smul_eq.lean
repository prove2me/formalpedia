-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_CommPf_smul_eq
-- name    : PositivityTheory.Rg.Sw.SP.CommPf.smul_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:59:16.300792+00:00
-- url     : https://prove2.me/theorems/39391652-1d06-4f8b-845e-fea09b8a7cd3
-- title:
--   Comm Pf: smul eq
-- statement:
--   The Comm Pf construction uses the smul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/DerivationConstantVanishes.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/DerivationConstantVanishes.lean#L30-L32

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_DerivationConstantVanishes
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
variable {n : ℕ}
open PositivityTheory.Rg.Sw.SP.CommPf

theorem PositivityTheory.Rg.Sw.SP.CommPf.smul_eq (c : ℂ) (p : Fm n) : c • p = MvPolynomial.C (Polynomial.C c) * p := by sorry
