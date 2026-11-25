-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Rs_JLatOf_mem_gmap
-- name    : PositivityTheory.Rg.Rs.JLatOf.mem_gmap
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:54:42.549805+00:00
-- url     : https://prove2.me/theorems/0a3877b6-0610-4c54-afd2-26b1ca0684cf
-- title:
--   JLat Of: mem gmap
-- statement:
--   The JLat Of construction uses the mem gmap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/ExponentialNegativity/LatticeReduction/LatticeHeightZeroEq.lean#L34-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/ExponentialNegativity/LatticeReduction/LatticeHeightZeroEq.lean#L34-L37

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

theorem PositivityTheory.Rg.Rs.JLatOf.mem_gmap {g : GL (Fin N) k} {M : Submodule k (Fin N → k)} {y : Fin N → k} :
    y ∈ gmap g M ↔ ∃ x ∈ M, (g : Matrix (Fin N) (Fin N) k) *ᵥ x = y := by sorry
