-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_length_quotient_eq_length_H0_0b4d02d4c4c7
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_length_quotient_eq_length_H0_0b4d02d4c4c7
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:12:15.770707+00:00
-- url     : https://prove2.me/theorems/e1d98178-205a-4cea-86e9-4bbda589b83c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict length quotient eq length H0 0b4d02d4c4c7: P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict length quotient eq length H0 0b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict length quotient eq length H0 0b4d02d4c4c7 construction uses the P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict length quotient eq length H0 0b4d02d4c4c7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrLenRestrict.lean#L49-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrLenRestrict.lean#L49-L56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrLenRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrLenRestrict
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
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.RestrLenRestrict
variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] {G : Cell U → Type w}
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}
  {M : Type w} [AddCommGroup M] [Module R M]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_length_quotient_eq_length_H0_0b4d02d4c4c7 (φ : M →ₗ[R] Cech.Cochain G 0) (hφ : ∀ m, Cech.d G ρ 0 (φ m) = 0)
    (h : ∀ z : Cech.Cochain G 0, Cech.d G ρ 0 z = 0 → ∃ m, φ m = z) (K : Submodule R M)
    (hK : ∀ m, φ m = 0 ↔ m ∈ K) : Module.length R (M ⧸ K) = Module.length R (Cech.H G ρ 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«RestrLenRestrict».«length_quotient_eq_length_H0» := P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_length_quotient_eq_length_H0_0b4d02d4c4c7
