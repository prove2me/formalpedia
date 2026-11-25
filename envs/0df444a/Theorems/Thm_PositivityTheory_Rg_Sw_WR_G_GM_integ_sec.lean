-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GM_integ_sec
-- name    : PositivityTheory.Rg.Sw.WR.G.GM.integ_sec
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:06:36.000801+00:00
-- url     : https://prove2.me/theorems/b19d4ed2-b0c4-5bc8-af23-d5760d4eeadb
-- title:
--   GM: integ sec
-- statement:
--   The GM construction uses the integ sec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GaussM.lean#L51-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GaussM.lean#L51-L60

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix MvPolynomial
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
open PositivityTheory.Rg.Sw.WR.G.GM

theorem PositivityTheory.Rg.Sw.WR.G.GM.integ_sec (hI : IntegP) {ε : Fin m → Bool} {c t : ℝ} (hc : 0 < c) {b : Matrix (Fin n) (Fin n) ℂ}
    (hb : b.IsHermitian) (P : PX m n) :
    Integrable fun x => evX P x * gs c x * Complex.exp (Complex.I * t * (b * gramX ε x).trace) := by sorry
