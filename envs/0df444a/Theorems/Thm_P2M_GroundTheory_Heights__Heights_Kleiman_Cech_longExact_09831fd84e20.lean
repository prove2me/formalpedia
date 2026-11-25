-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_longExact_09831fd84e20
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Cech_longExact_09831fd84e20
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:26.239709+00:00
-- url     : https://prove2.me/theorems/a049347b-ed1e-4c5d-81d3-9ebc7c3e492e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech long Exact 09831fd84e20: P2 M Ground Theory Heights  Heights Kleiman Cech long Exact 09831fd84e20
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech long Exact 09831fd84e20 construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech long Exact 09831fd84e20 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechExact.lean#L157-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechExact.lean#L157-L258

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Cech_longExact_09831fd84e20 (hφ : ∀ I J h m, φ J (ρA I J h m) = ρB I J h (φ I m))
    (hψ : ∀ I J h m, ψ J (ρB I J h m) = ρC I J h (ψ I m))
    (hφd : ∀ I m, m ∈ dA I → φ I m ∈ dB I) (hψd : ∀ I m, m ∈ dB I → ψ I m ∈ dC I)
    (hinj : ∀ I, Function.Injective (φ I)) (hcomp : ∀ I x, ψ I (φ I x) = 0)
    (hmid : ∀ I, ∀ x ∈ dB I, ψ I x = 0 → ∃ y ∈ dA I, φ I y = x)
    (hsurj : ∀ I, ∀ z ∈ dC I, ∃ x ∈ dB I, ψ I x = z)
    (hρB : ∀ I J h x, x ∈ dB I → ρB I J h x ∈ dB J)
    (hddB : ∀ (i : ℕ) (s : Cochain B i), d B ρB (i + 1) (d B ρB i s) = 0) :
    Function.Injective (mapHdeg dA dB φ hφ hφd 0) ∧
      ∀ i : ℕ, Function.Exact (mapHdeg dA dB φ hφ hφd i) (mapHdeg dB dC ψ hψ hψd i) ∧
        ∃ δ : Hdeg C dC ρC i →ₗ[R] Hdeg A dA ρA (i + 1),
          Function.Exact (mapHdeg dB dC ψ hψ hψd i) δ ∧ Function.Exact δ (mapHdeg dA dB φ hφ hφd (i + 1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Cech».«longExact» := P2M_GroundTheory_Heights__Heights_Kleiman_Cech_longExact_09831fd84e20
