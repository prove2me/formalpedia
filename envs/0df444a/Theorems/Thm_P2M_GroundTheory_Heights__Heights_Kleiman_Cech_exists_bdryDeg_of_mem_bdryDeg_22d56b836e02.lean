-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_exists_bdryDeg_of_mem_bdryDeg_22d56b836e02
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Cech_exists_bdryDeg_of_mem_bdryDeg_22d56b836e02
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:32.165042+00:00
-- url     : https://prove2.me/theorems/88dfe9fb-d526-4a8f-b224-322c525c8763
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech exists bdry Deg of mem bdry Deg 22d56b836e02: P2 M Ground Theory Heights  Heights Kleiman Cech exists bdry Deg of mem bdry Deg 22d56b836e02
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech exists bdry Deg of mem bdry Deg 22d56b836e02 construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech exists bdry Deg of mem bdry Deg 22d56b836e02 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechExact.lean#L91-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechExact.lean#L91-L105

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Cech_exists_bdryDeg_of_mem_bdryDeg_22d56b836e02 (hψ : ∀ I J h m, ψ J (ρB I J h m) = ρC I J h (ψ I m))
    (hsurj : ∀ I, ∀ z ∈ dC I, ∃ x ∈ dB I, ψ I x = z)
    (hρB : ∀ I J h x, x ∈ dB I → ρB I J h x ∈ dB J)
    (hddB : ∀ (i : ℕ) (s : Cochain B i), d B ρB (i + 1) (d B ρB i s) = 0) {i : ℕ}
    {s : Cochain C i} (hs : s ∈ bdryDeg C dC ρC i) :
    ∃ x, x ∈ bdryDeg B dB ρB i ∧ x ∈ Cdeg B dB i ∧ mapC ψ i x = s ∧ d B ρB i x = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Cech».«exists_bdryDeg_of_mem_bdryDeg» := P2M_GroundTheory_Heights__Heights_Kleiman_Cech_exists_bdryDeg_of_mem_bdryDeg_22d56b836e02
