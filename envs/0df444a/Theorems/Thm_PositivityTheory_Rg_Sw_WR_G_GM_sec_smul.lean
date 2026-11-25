-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GM_sec_smul
-- name    : PositivityTheory.Rg.Sw.WR.G.GM.sec_smul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:06:10.824568+00:00
-- url     : https://prove2.me/theorems/65fdab21-8915-5605-b5cc-2ad3ee6c4e45
-- title:
--   GM: sec smul
-- statement:
--   The GM construction uses the sec smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GaussM.lean#L68-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GaussM.lean#L68-L72

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

theorem PositivityTheory.Rg.Sw.WR.G.GM.sec_smul {ε : Fin m → Bool} {c t : ℝ} {b : Matrix (Fin n) (Fin n) ℂ} (r : ℂ) (P : PX m n) :
    secN ε c t (r • P) b = r * secN ε c t P b := by sorry
