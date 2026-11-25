-- Prove2me | Theorems.Thm_P2M_GroundTheory_Arith_SchemeCoh_towerComp_comp_of_comm__9e39104e9438
-- name    : P2M_GroundTheory_Arith_SchemeCoh_towerComp_comp_of_comm__9e39104e9438
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:12:50.776328+00:00
-- url     : https://prove2.me/theorems/00566dcb-162b-4d22-a35b-aa891c1678a4
-- title:
--   P2 M Ground Theory Arith Scheme Coh tower Comp comp of comm  9e39104e9438: P2 M Ground Theory Arith Scheme Coh tower Comp comp of comm  9e39104e9438
-- statement:
--   The P2 M Ground Theory Arith Scheme Coh tower Comp comp of comm  9e39104e9438 construction uses the P2 M Ground Theory Arith Scheme Coh tower Comp comp of comm  9e39104e9438 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/FormalLimit.lean#L99-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/FormalLimit.lean#L99-L101

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_FormalLimit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
universe u
noncomputable section
variable {A : Type u} [CommRing A]
  {P E Q : ℕ → Type u} [∀ n, AddCommGroup (P n)] [∀ n, Module A (P n)]
  [∀ n, AddCommGroup (E n)] [∀ n, Module A (E n)] [∀ n, AddCommGroup (Q n)]
  [∀ n, Module A (Q n)]
  (τP : ∀ n, P (n + 1) →ₗ[A] P n) (τE : ∀ n, E (n + 1) →ₗ[A] E n) (τQ : ∀ n, Q (n + 1) →ₗ[A] Q n)
  (ι : ∀ n, P n →ₗ[A] E n) (π : ∀ n, E n →ₗ[A] Q n)
  (hι : ∀ n, (τE n).comp (ι (n + 1)) = (ι n).comp (τP n))
  (hπ : ∀ n, (τQ n).comp (π (n + 1)) = (π n).comp (τE n))
include hπ

theorem P2M_GroundTheory_Arith_SchemeCoh_towerComp_comp_of_comm__9e39104e9438 (n k : ℕ) :
    (towerComp τQ n k).comp (π (n + k)) = (π n).comp (towerComp τE n k) := by sorry

alias «GroundTheory».«Arith».«SchemeCoh».«towerComp_comp_of_comm'» := P2M_GroundTheory_Arith_SchemeCoh_towerComp_comp_of_comm__9e39104e9438
