-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_exists_mapC_eq_of_mem_e11fe874719c
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Cech_exists_mapC_eq_of_mem_e11fe874719c
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:29.22064+00:00
-- url     : https://prove2.me/theorems/7c874107-fcb2-4a87-8a45-98d2c21af823
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech exists map C eq of mem e11fe874719c: P2 M Ground Theory Heights  Heights Kleiman Cech exists map C eq of mem e11fe874719c
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech exists map C eq of mem e11fe874719c construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech exists map C eq of mem e11fe874719c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechExact.lean#L80-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechExact.lean#L80-L83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsDegLocExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v
open GroundTheory.Heights₂.Heights.Kleiman.Cech
variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R]
  {A B C : Cell U → Type v}
  [∀ I, AddCommGroup (A I)] [∀ I, Module R (A I)]
  [∀ I, AddCommGroup (B I)] [∀ I, Module R (B I)]
  [∀ I, AddCommGroup (C I)] [∀ I, Module R (C I)]
  {ρA : ∀ I J : Cell U, I.1 ⊆ J.1 → A I →ₗ[R] A J}
  {ρB : ∀ I J : Cell U, I.1 ⊆ J.1 → B I →ₗ[R] B J}
  {ρC : ∀ I J : Cell U, I.1 ⊆ J.1 → C I →ₗ[R] C J}
  {dA : ∀ I, Submodule R (A I)} {dB : ∀ I, Submodule R (B I)} {dC : ∀ I, Submodule R (C I)}
  {φ : ∀ I, A I →ₗ[R] B I} {ψ : ∀ I, B I →ₗ[R] C I}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Cech_exists_mapC_eq_of_mem_e11fe874719c (hsurj : ∀ I, ∀ z ∈ dC I, ∃ x ∈ dB I, ψ I x = z) {i : ℕ}
    {s : Cochain C i} (hs : s ∈ Cdeg C dC i) : ∃ t ∈ Cdeg B dB i, mapC ψ i t = s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Cech».«exists_mapC_eq_of_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_Cech_exists_mapC_eq_of_mem_e11fe874719c
