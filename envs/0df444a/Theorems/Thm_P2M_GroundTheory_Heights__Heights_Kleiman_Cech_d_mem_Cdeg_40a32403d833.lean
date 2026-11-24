-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_d_mem_Cdeg_40a32403d833
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Cech_d_mem_Cdeg_40a32403d833
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:26.938945+00:00
-- url     : https://prove2.me/theorems/b2f6bd92-8cb7-4919-9e2e-fdaa61f49b44
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech d mem Cdeg 40a32403d833: P2 M Ground Theory Heights  Heights Kleiman Cech d mem Cdeg 40a32403d833
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech d mem Cdeg 40a32403d833 construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech d mem Cdeg 40a32403d833 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechExact.lean#L85-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechExact.lean#L85-L89

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Cech_d_mem_Cdeg_40a32403d833 (hρB : ∀ I J h x, x ∈ dB I → ρB I J h x ∈ dB J) {i : ℕ} {s : Cochain B i}
    (hs : s ∈ Cdeg B dB i) : d B ρB i s ∈ Cdeg B dB (i + 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Cech».«d_mem_Cdeg» := P2M_GroundTheory_Heights__Heights_Kleiman_Cech_d_mem_Cdeg_40a32403d833
