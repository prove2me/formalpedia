-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_CA_height_le_height_comap_of_eval__surjective_53198ccc5ac1
-- name    : P2M_ReciprocityTheory_CA_height_le_height_comap_of_eval__surjective_53198ccc5ac1
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:43:38.444215+00:00
-- url     : https://prove2.me/theorems/4f9c5dca-4b1c-4380-a876-5102b39a8479
-- title:
--   P2 M Reciprocity Theory CA height le height comap of eval  surjective 53198ccc5ac1: P2 M Reciprocity Theory CA height le height comap of eval  surjective 53198ccc5ac1
-- statement:
--   The P2 M Reciprocity Theory CA height le height comap of eval  surjective 53198ccc5ac1 construction uses the P2 M Reciprocity Theory CA height le height comap of eval  surjective 53198ccc5ac1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/SaturatedChains/AlgStep.lean#L102-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/SaturatedChains/AlgStep.lean#L102-L123

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

theorem P2M_ReciprocityTheory_CA_height_le_height_comap_of_eval__surjective_53198ccc5ac1 {R S : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [CommRing S] [IsDomain S] (f : R →+* S) (hf : Function.Injective f) (x : S)
    (hgen : Function.Surjective (eval₂RingHom f x)) (halg : ∃ g : R[X], g ≠ 0 ∧ eval₂ f x g = 0)
    (q : Ideal S) [q.IsPrime] : q.height ≤ (q.comap f).height := by sorry

alias «ReciprocityTheory».«CA».«height_le_height_comap_of_eval₂_surjective» := P2M_ReciprocityTheory_CA_height_le_height_comap_of_eval__surjective_53198ccc5ac1
