-- Prove2me | Theorems.Thm_ValuationSubring_dvd_padicValRat_of_inertia_fixed_radical
-- name    : ValuationSubring.dvd_padicValRat_of_inertia_fixed_radical
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:01:44.228226+00:00
-- url     : https://prove2.me/theorems/b57bd28c-25da-42f3-a20e-5dce5e3b3679
-- title:
--   An inertia-fixed radical forces divisibility of the rational p-adic valuation
-- statement:
--   Let $q$ be prime, let $A$ be a valuation subring of $\overline{ℚ}$ above $q$, let $m∈ℕ$, let $a∈ℚ^{×}$, and let $α∈\overline{ℚ}^{×}$ satisfy $α^m=a$. If every element of the inertia group of $A/ℚ$ fixes $α$, then $$(m:ℤ)\mid v_q(a).$$ This is the local Kummer-theoretic step converting inertia invariance into valuation divisibility.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn
import Theorems.Thm_ValuationSubring_valuation_ratCast_eq_zpow_padicValRat

set_option autoImplicit false
open ValuationSubring

theorem ValuationSubring.dvd_padicValRat_of_inertia_fixed_radical
    (A : ValuationSubring (AlgebraicClosure ℚ)) (q : ℕ) [Fact q.Prime]
    (hA : A.LiesOverPrime q) (m : ℕ) (a : ℚˣ) (α : (AlgebraicClosure ℚ)ˣ)
    (hα : (α : AlgebraicClosure ℚ) ^ m = (a : ℚ))
    (hfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ (α : AlgebraicClosure ℚ) = α) :
    (m : ℤ) ∣ padicValRat q (a : ℚ) := by sorry
