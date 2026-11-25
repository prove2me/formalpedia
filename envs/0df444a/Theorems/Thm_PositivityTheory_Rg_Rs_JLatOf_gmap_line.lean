-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Rs_JLatOf_gmap_line
-- name    : PositivityTheory.Rg.Rs.JLatOf.gmap_line
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:52:24.942872+00:00
-- url     : https://prove2.me/theorems/e5f44cc3-babe-5797-9bf8-7f3483aeb0e6
-- title:
--   JLat Of: gmap line
-- statement:
--   The JLat Of construction uses the gmap line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/ExponentialNegativity/LatticeReduction/LatticeHeightZeroEq.lean#L196-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/ExponentialNegativity/LatticeReduction/LatticeHeightZeroEq.lean#L196-L220

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

theorem PositivityTheory.Rg.Rs.JLatOf.gmap_line (g : GL (Fin N) k) (i₀ : Fin N) (h0 : ∀ a, a ≠ i₀ → (g : Matrix (Fin N) (Fin N) k) a i₀ = 0) :
    gmap g (Submodule.span k {(Pi.single i₀ (1 : k) : Fin N → k)}) =
      Submodule.span k {(Pi.single i₀ (1 : k) : Fin N → k)} := by sorry
