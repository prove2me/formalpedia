-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Rs_JLatOf_finrank_gmap
-- name    : PositivityTheory.Rg.Rs.JLatOf.finrank_gmap
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:50:13.054116+00:00
-- url     : https://prove2.me/theorems/7b2f9add-42d2-4181-bcf0-a514d4b7ad43
-- title:
--   JLat Of: finrank gmap
-- statement:
--   The JLat Of construction uses the finrank gmap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/ExponentialNegativity/LatticeReduction/LatticeHeightZeroEq.lean#L56-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/ExponentialNegativity/LatticeReduction/LatticeHeightZeroEq.lean#L56-L62

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

theorem PositivityTheory.Rg.Rs.JLatOf.finrank_gmap (g : GL (Fin N) k) (M : Submodule k (Fin N → k)) :
    finrank k (gmap g M) = finrank k M := by sorry
