-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_height_add_one_le_height_comap_of_surjective
-- name    : ReciprocityTheory.CA.height_add_one_le_height_comap_of_surjective
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:39:27.328329+00:00
-- url     : https://prove2.me/theorems/a63ebac6-4f00-50d1-9a26-bb839dd55310
-- title:
--   CA: height add one le height comap of surjective
-- statement:
--   The CA construction uses the height add one le height comap of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/SaturatedChains/AlgStep.lean#L71-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/SaturatedChains/AlgStep.lean#L71-L100

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_IsSaturatedChain
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_AlgStep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open Polynomial

theorem ReciprocityTheory.CA.height_add_one_le_height_comap_of_surjective {A S : Type*} [CommRing A] [IsDomain A]
    [CommRing S] (φ : A →+* S) (hφ : Function.Surjective φ) (hker : RingHom.ker φ ≠ ⊥)
    (q : Ideal S) [q.IsPrime] : q.height + 1 ≤ (q.comap φ).height := by sorry
