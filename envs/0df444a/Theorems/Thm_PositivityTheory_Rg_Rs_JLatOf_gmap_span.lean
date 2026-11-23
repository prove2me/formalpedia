-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Rs_JLatOf_gmap_span
-- name    : PositivityTheory.Rg.Rs.JLatOf.gmap_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:45.570973+00:00
-- url     : https://prove2.me/theorems/d79de0c0-8a45-41f6-927b-546632097ea1
-- title:
--   JLat Of: gmap span
-- statement:
--   The JLat Of construction uses the gmap span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/ExponentialNegativity/LatticeReduction/LatticeHeightZeroEq.lean#L154-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/ExponentialNegativity/LatticeReduction/LatticeHeightZeroEq.lean#L154-L159

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

theorem PositivityTheory.Rg.Rs.JLatOf.gmap_span {ι : Type} (g : GL (Fin N) k) (u : ι → Fin N → k) :
    gmap g (Submodule.span k (Set.range u)) =
      Submodule.span k (Set.range fun i => (g : Matrix (Fin N) (Fin N) k) *ᵥ u i) := by sorry
