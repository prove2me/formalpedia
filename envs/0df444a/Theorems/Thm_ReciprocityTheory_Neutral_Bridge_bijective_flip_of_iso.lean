-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Bridge_bijective_flip_of_iso
-- name    : ReciprocityTheory.Neutral.Bridge.bijective_flip_of_iso
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:05:11.319147+00:00
-- url     : https://prove2.me/theorems/1b4b9541-3ff3-4b9e-b5ba-cca6ab0cba32
-- title:
--   Bridge: bijective flip of iso
-- statement:
--   The Bridge construction uses the bijective flip of iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/TransportA.lean#L217-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/TransportA.lean#L217-L221

import Definitions.Def_ReciprocityTheory_Hypotheses_GalCohDefs
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TransportA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Bridge
open ReciprocityTheory.Gal
variable {R : Type*} [CommRing R] {A A' B B' C C' : Type*}
  [AddCommGroup A] [Module R A] [AddCommGroup A'] [Module R A']
  [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R B']
  [AddCommGroup C] [Module R C] [AddCommGroup C'] [Module R C']

theorem ReciprocityTheory.Neutral.Bridge.bijective_flip_of_iso (α : A ≃ₗ[R] A') (β : B ≃ₗ[R] B') (γ : C ≃ₗ[R] C')
    (f : A →ₗ[R] B →ₗ[R] C) (f' : A' →ₗ[R] B' →ₗ[R] C')
    (h : ∀ a b, f' (α a) (β b) = γ (f a b)) (hf : Function.Bijective f'.flip) :
    Function.Bijective f.flip := by sorry
