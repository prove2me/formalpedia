-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_mapC_mapC_eq_zero_c24cc487b19e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Cech_mapC_mapC_eq_zero_c24cc487b19e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:06.347013+00:00
-- url     : https://prove2.me/theorems/a8f33128-5a3b-4d0d-8baa-36fbac7a0fef
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech map C map C eq zero c24cc487b19e: P2 M Ground Theory Heights  Heights Kleiman Cech map C map C eq zero c24cc487b19e
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech map C map C eq zero c24cc487b19e construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech map C map C eq zero c24cc487b19e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechExact.lean#L70-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechExact.lean#L70-L72

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Cech_mapC_mapC_eq_zero_c24cc487b19e (hcomp : ∀ I x, ψ I (φ I x) = 0) (i : ℕ) (s : Cochain A i) :
    mapC ψ i (mapC φ i s) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Cech».«mapC_mapC_eq_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_Cech_mapC_mapC_eq_zero_c24cc487b19e
