-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Rs_JLatOf_span_basis_coe
-- name    : PositivityTheory.Rg.Rs.JLatOf.span_basis_coe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:28.710515+00:00
-- url     : https://prove2.me/theorems/9927476f-1420-42d6-b8f0-e89b4896dc8d
-- title:
--   JLat Of: span basis coe
-- statement:
--   The JLat Of construction uses the span basis coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/ExponentialNegativity/LatticeReduction/LatticeHeightZeroEq.lean#L161-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/ExponentialNegativity/LatticeReduction/LatticeHeightZeroEq.lean#L161-L166

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

theorem PositivityTheory.Rg.Rs.JLatOf.span_basis_coe {ι : Type} {M : Submodule k (Fin N → k)} (b : Basis ι k M) :
    Submodule.span k (Set.range fun i => (b i : Fin N → k)) = M := by sorry
