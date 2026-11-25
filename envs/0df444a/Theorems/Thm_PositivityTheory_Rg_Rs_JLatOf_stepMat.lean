-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Rs_JLatOf_stepMat
-- name    : PositivityTheory.Rg.Rs.JLatOf.stepMat
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:52:58.680903+00:00
-- url     : https://prove2.me/theorems/8ff088e0-7944-40d9-8387-38ca78069467
-- title:
--   JLat Of: step Mat
-- statement:
--   The JLat Of construction uses the step Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/ExponentialNegativity/LatticeReduction/LatticeHeightZeroEq.lean#L234-L340
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/ExponentialNegativity/LatticeReduction/LatticeHeightZeroEq.lean#L234-L340

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

theorem PositivityTheory.Rg.Rs.JLatOf.stepMat [Finite k] (n : ℕ) (M : Submodule k (Fin (n + 1) → k)) (hM : e0 k n ∈ M) :
    ∃ (jj : Fin (n + 1)) (g : GL (Fin (n + 1)) k), (jj : ℕ) + finrank k M = n + 1 ∧
      gmap g (Mj k (n + 1) jj) = M ∧ gmap g (Mj k (n + 1) (jj + 1)) = M ⊓ H0 k n ∧
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ Pi.single jj 1 = e0 k n ∧
      ∀ b : Fin (n + 1), jj < b → (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) 0 b = 0 := by sorry
