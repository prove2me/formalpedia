-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_cechH0Map_injective_562dc05f7cb3
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_cechH0Map_injective_562dc05f7cb3
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:57:44.272055+00:00
-- url     : https://prove2.me/theorems/da576964-8dbc-5817-b26d-3ab7e5c1f987
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term cech H0 Map injective 562dc05f7cb3: P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term cech H0 Map injective 562dc0
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term cech H0 Map injective 562dc05f7cb3 construction uses the P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term cech H0 Map injective 562dc05f7cb3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropTerm.lean#L226-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropTerm.lean#L226-L244

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropTermSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotSectionsFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountDropTerm
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
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.SectionCount GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Term
variable {n : ℕ} {U : Finset (Fin n)} {R : Type*} [CommRing R]
  {G G' : Cell U → Type*} [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)]
  [∀ I, AddCommGroup (G' I)] [∀ I, Module R (G' I)]
  {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J} {ρ' : ∀ I J : Cell U, I.1 ⊆ J.1 → G' I →ₗ[R] G' J}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_cechH0Map_injective_562dc05f7cb3 (φ : ∀ I, G I →ₗ[R] G' I) (hφ : ∀ I J h m, φ J (ρ I J h m) = ρ' I J h (φ I m))
    (hinj : ∀ I : Cech.Idx U 0, Function.Injective (φ I.1)) : Function.Injective (cechH0Map φ hφ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionCount».«Drop».«Term».«cechH0Map_injective» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_cechH0Map_injective_562dc05f7cb3
