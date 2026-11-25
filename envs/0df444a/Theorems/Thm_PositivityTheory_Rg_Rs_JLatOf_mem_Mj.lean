-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Rs_JLatOf_mem_Mj
-- name    : PositivityTheory.Rg.Rs.JLatOf.mem_Mj
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:48:38.15355+00:00
-- url     : https://prove2.me/theorems/c47b2cfc-c90b-49ba-9455-c85f9f12724e
-- title:
--   JLat Of: mem Mj
-- statement:
--   The JLat Of construction uses the mem Mj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/ExponentialNegativity/LatticeReduction/LatticeHeightZeroEq.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/ExponentialNegativity/LatticeReduction/LatticeHeightZeroEq.lean#L26-L27

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_GapAbsOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_LatticeReduction_LatticeHeightZeroEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Module
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.JLatOf
open PositivityTheory.Rg.Rs
variable {k : Type} [Field k] {N : ℕ}

theorem PositivityTheory.Rg.Rs.JLatOf.mem_Mj {j : ℕ} {x : Fin N → k} : x ∈ Mj k N j ↔ ∀ a : Fin N, (a : ℕ) < j → x a = 0 := by sorry
