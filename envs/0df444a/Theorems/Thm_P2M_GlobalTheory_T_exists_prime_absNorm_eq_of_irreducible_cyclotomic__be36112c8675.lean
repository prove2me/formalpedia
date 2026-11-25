-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_prime_absNorm_eq_of_irreducible_cyclotomic__be36112c8675
-- name    : P2M_GlobalTheory_T_exists_prime_absNorm_eq_of_irreducible_cyclotomic__be36112c8675
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:13:19.521897+00:00
-- url     : https://prove2.me/theorems/9deed374-d211-4071-aed4-feb828b6aac2
-- title:
--   P2 M Global Theory T exists prime abs Norm eq of irreducible cyclotomic  be36112c8675: P2 M Global Theory T exists prime abs Norm eq of irreducible cyclotomic  be36112c8675
-- statement:
--   The P2 M Global Theory T exists prime abs Norm eq of irreducible cyclotomic  be36112c8675 construction uses the P2 M Global Theory T exists prime abs Norm eq of irreducible cyclotomic  be36112c8675 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPrimeAbsNormEqOfIrreducibleCyclotomicStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPrimeAbsNormEqOfIrreducibleCyclotomicStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPrimeAbsNormEqOfIrreducibleCyclotomic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealCharacterLContinuationNeZeroOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPrimeAbsNormEqOfIrreducibleCyclotomicStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_prime_absNorm_eq_of_irreducible_cyclotomic__be36112c8675 : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ), m.Prime → Irreducible (cyclotomic m K) → ∀ (τ : (ZMod m)ˣ) (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite → ∃ P : HeightOneSpectrum (𝓞 K), P ∉ S ∧ (Ideal.absNorm P.asIdeal).Prime ∧ ((Ideal.absNorm P.asIdeal : ℕ) : ZMod m) = (τ : ZMod m) := by sorry

alias «GlobalTheory».«T».«exists_prime_absNorm_eq_of_irreducible_cyclotomic'» := P2M_GlobalTheory_T_exists_prime_absNorm_eq_of_irreducible_cyclotomic__be36112c8675
