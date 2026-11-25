-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_DegLT_sub
-- name    : PositivityTheory.Rg.Sw.LC.Basic.DegLT.sub
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:56:22.321978+00:00
-- url     : https://prove2.me/theorems/4fa4b1a5-a8fb-4da8-b544-2d48741b0ed1
-- title:
--   Deg LT: sub
-- statement:
--   The Deg LT construction uses the sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/MapDomainFlpFlp.lean#L146-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/MapDomainFlpFlp.lean#L146-L147

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MapDomainFlpFlp
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.Basic
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.LC.Basic.DegLT.sub {d : ℕ} {P Q : PX m n} (hP : DegLT d P) (hQ : DegLT d Q) : DegLT d (P - Q) := by sorry
