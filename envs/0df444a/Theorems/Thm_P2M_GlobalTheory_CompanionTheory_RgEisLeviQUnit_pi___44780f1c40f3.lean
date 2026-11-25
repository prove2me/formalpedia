-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_RgEisLeviQUnit_pi___44780f1c40f3
-- name    : P2M_GlobalTheory_CompanionTheory_RgEisLeviQUnit_pi___44780f1c40f3
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:03:26.161111+00:00
-- url     : https://prove2.me/theorems/91a473ff-56e6-40dd-884e-c9d2d108254a
-- title:
--   P2 M Global Theory Companion Theory Rg Eis Levi QUnit pi   44780f1c40f3: P2 M Global Theory Companion Theory Rg Eis Levi QUnit pi   44780f1c40f3
-- statement:
--   The P2 M Global Theory Companion Theory Rg Eis Levi QUnit pi   44780f1c40f3 construction uses the P2 M Global Theory Companion Theory Rg Eis Levi QUnit pi   44780f1c40f3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L569-L584
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L569-L584

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviQuotientOfBlockDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisLeviQUnit
open PositivityTheory.RgEis
variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set ι}
  [Fintype ↥sᶜ] [DecidableEq ↥sᶜ] (A : Ad E R) (ε : ℤˣ) (hσ : ∀ x, A.σ (A.σ x) = x)
include hσ

theorem P2M_GlobalTheory_CompanionTheory_RgEisLeviQUnit_pi___44780f1c40f3 (hi : Function.Injective A.i) (q : A.uQ ε s) (hq : (q : A.U ε ι) ∈ A.uΓ ε ι) :
    piQ A ε hσ q ∈ A.uΓ ε ↥sᶜ := by sorry

alias «GlobalTheory».«CompanionTheory».«RgEisLeviQUnit».«pi_Γ» := P2M_GlobalTheory_CompanionTheory_RgEisLeviQUnit_pi___44780f1c40f3
