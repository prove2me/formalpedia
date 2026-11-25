-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_RgEisLeviQUnit_c__par_21c7392b8182
-- name    : P2M_GlobalTheory_CompanionTheory_RgEisLeviQUnit_c__par_21c7392b8182
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:02:55.894678+00:00
-- url     : https://prove2.me/theorems/01223424-466a-41ab-a183-a1f032f0dbbb
-- title:
--   P2 M Global Theory Companion Theory Rg Eis Levi QUnit c  par 21c7392b8182: P2 M Global Theory Companion Theory Rg Eis Levi QUnit c  par 21c7392b8182
-- statement:
--   The P2 M Global Theory Companion Theory Rg Eis Levi QUnit c  par 21c7392b8182 construction uses the P2 M Global Theory Companion Theory Rg Eis Levi QUnit c  par 21c7392b8182 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L726-L741
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L726-L741

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
variable {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] (A : Ad E R) (ε : ℤˣ)
variable {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set ι} {_fF : Fintype ↥sᶜ} {_fD : DecidableEq ↥sᶜ}

theorem P2M_GlobalTheory_CompanionTheory_RgEisLeviQUnit_c__par_21c7392b8182 (hB : BdetLaw) (hA : A.Good) (hI : Iwa (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uK ε ι)) :
    IsPar (A.uΓ ε ι) (A.uK ε ι) (A.uQ ε s) (c₀ A ε s) := by sorry

alias «GlobalTheory».«CompanionTheory».«RgEisLeviQUnit».«c₀_par» := P2M_GlobalTheory_CompanionTheory_RgEisLeviQUnit_c__par_21c7392b8182
