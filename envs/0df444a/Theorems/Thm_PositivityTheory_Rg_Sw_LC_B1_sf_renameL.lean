-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_sf_renameL
-- name    : PositivityTheory.Rg.Sw.LC.B1.sf_renameL
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:56:11.338944+00:00
-- url     : https://prove2.me/theorems/10ee8e93-f4c5-50a1-9b51-5de8c4f0065a
-- title:
--   B1: sf rename L
-- statement:
--   The B1 construction uses the sf rename L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PderivPowMonomial.lean#L224-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PderivPowMonomial.lean#L224-L230

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivPowMonomial
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.B1
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
local notation "σ" => Fin m × Fin n × Bool
variable (ε : Fin m → Bool)

theorem PositivityTheory.Rg.Sw.LC.B1.sf_renameL (p : PX m n) (hp : p ∈ F1 ε) {s : Sym m n} (h : SymbolInFirstFamily ε s) : SymbolInFirstFamily ε (rename Sum.inl p * s) := by sorry
