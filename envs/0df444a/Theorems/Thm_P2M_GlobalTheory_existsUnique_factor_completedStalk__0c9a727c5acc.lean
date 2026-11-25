-- Prove2me | Theorems.Thm_P2M_GlobalTheory_existsUnique_factor_completedStalk__0c9a727c5acc
-- name    : P2M_GlobalTheory_existsUnique_factor_completedStalk__0c9a727c5acc
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:06:48.082057+00:00
-- url     : https://prove2.me/theorems/1aca51ed-3384-4513-b1c4-f5d52d1a0e8d
-- title:
--   P2 M Global Theory exists Unique factor completed Stalk  0c9a727c5acc: P2 M Global Theory exists Unique factor completed Stalk  0c9a727c5acc
-- statement:
--   The P2 M Global Theory exists Unique factor completed Stalk  0c9a727c5acc construction uses the P2 M Global Theory exists Unique factor completed Stalk  0c9a727c5acc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L158-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L158-L168

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry IsLocalRing
universe u
open GlobalTheory
variable {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
omit [IsLocalRing R]

theorem P2M_GlobalTheory_existsUnique_factor_completedStalk__0c9a727c5acc (I : Ideal R) [IsAdicComplete I R]
    {f : Spec (.of R) ⟶ X} {x : X}
    {φ : X.presheaf.stalk x ⟶ .of R} (hφ : Spec.map φ ≫ X.fromSpecStalk x = f)
    (hfg : (maximalIdeal (X.presheaf.stalk x)).FG)
    (hk : ∃ k : ℕ, (maximalIdeal (X.presheaf.stalk x)).map φ.hom ^ k ≤ I) :
    ∃! g, g ≫ fromSpecCompletedStalk X x = f := by sorry

alias «GlobalTheory».«existsUnique_factor_completedStalk'» := P2M_GlobalTheory_existsUnique_factor_completedStalk__0c9a727c5acc
