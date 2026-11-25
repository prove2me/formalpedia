-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_contr_add
-- name    : PositivityTheory.Rg.Sw.LC.contr_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:44:39.34111+00:00
-- url     : https://prove2.me/theorems/612c3e5d-d839-4ea0-9246-6446654b59b3
-- title:
--   LC: contr add
-- statement:
--   The LC construction uses the contr add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ContrEqOfSubset.lean#L46-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ContrEqOfSubset.lean#L46-L52

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_GaussianMomentRecurrence
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ContrEqOfSubset
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

theorem PositivityTheory.Rg.Sw.LC.contr_add (c : ℝ) (p q : PX m n) : contr c (p + q) = contr c p + contr c q := by sorry
