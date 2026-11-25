-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_RgEisLeviQUnit_j___a51c829f7f74
-- name    : P2M_GlobalTheory_CompanionTheory_RgEisLeviQUnit_j___a51c829f7f74
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:02:50.67459+00:00
-- url     : https://prove2.me/theorems/4cec6b43-18c3-4350-ade6-1c1ec2e000ae
-- title:
--   P2 M Global Theory Companion Theory Rg Eis Levi QUnit j   a51c829f7f74: P2 M Global Theory Companion Theory Rg Eis Levi QUnit j   a51c829f7f74
-- statement:
--   The P2 M Global Theory Companion Theory Rg Eis Levi QUnit j   a51c829f7f74 construction uses the P2 M Global Theory Companion Theory Rg Eis Levi QUnit j   a51c829f7f74 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L586-L592
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L586-L592

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

theorem P2M_GlobalTheory_CompanionTheory_RgEisLeviQUnit_j___a51c829f7f74 (m : A.U ε ↥sᶜ) (hm : m ∈ A.uΓ ε ↥sᶜ) : (jQ (s := s) A ε m : A.U ε ι) ∈ A.uΓ ε ι := by sorry

alias «GlobalTheory».«CompanionTheory».«RgEisLeviQUnit».«j_Γ» := P2M_GlobalTheory_CompanionTheory_RgEisLeviQUnit_j___a51c829f7f74
