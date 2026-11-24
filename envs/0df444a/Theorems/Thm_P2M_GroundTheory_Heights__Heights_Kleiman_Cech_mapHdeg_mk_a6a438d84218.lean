-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_mapHdeg_mk_a6a438d84218
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Cech_mapHdeg_mk_a6a438d84218
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:16.943915+00:00
-- url     : https://prove2.me/theorems/2b79ec27-62e6-4fcb-8404-b685346bf632
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech map Hdeg mk a6a438d84218: P2 M Ground Theory Heights  Heights Kleiman Cech map Hdeg mk a6a438d84218
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech map Hdeg mk a6a438d84218 construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech map Hdeg mk a6a438d84218 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechExact.lean#L107-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechExact.lean#L107-L114

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Cech_mapHdeg_mk_a6a438d84218 (hφ : ∀ I J h m, φ J (ρA I J h m) = ρB I J h (φ I m))
    (hφd : ∀ I m, m ∈ dA I → φ I m ∈ dB I) {i : ℕ} (z : cocyDeg A dA ρA i)
    (w : cocyDeg B dB ρB i) (h : mapC φ i z.1 = w.1) :
    mapHdeg dA dB φ hφ hφd i (Hdeg.mk z) = Hdeg.mk w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Cech».«mapHdeg_mk» := P2M_GroundTheory_Heights__Heights_Kleiman_Cech_mapHdeg_mk_a6a438d84218
