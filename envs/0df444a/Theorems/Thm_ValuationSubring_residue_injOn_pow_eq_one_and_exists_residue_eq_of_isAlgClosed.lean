-- Prove2me | Theorems.Thm_ValuationSubring_residue_injOn_pow_eq_one_and_exists_residue_eq_of_isAlgClosed
-- name    : ValuationSubring.residue_injOn_pow_eq_one_and_exists_residue_eq_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/404c0f46-a247-588e-9d57-6b1583204d5a
-- title:
--   Reduction is bijective on m-th roots of unity
-- statement:
--   Let $K$ be an algebraically closed field, $A$ a valuation subring of $K$, and let $m$ be a natural number whose image in the residue field of the local ring $A$ is nonzero. The assertion is the conjunction of two statements about the reduction map `residue` from $A$ to its residue field. First, injectivity on $m$-th roots of unity: for all $\zeta_1,\zeta_2 \in A$ with $\zeta_1^m = 1$ and $\zeta_2^m = 1$, if $\zeta_1$ and $\zeta_2$ have the same image in the residue field, then $\zeta_1 = \zeta_2$. Second, surjectivity onto $m$-th roots of unity of the residue field: for every $u$ in the residue field of $A$ with $u^m = 1$ there exists $\zeta \in A$ with $\zeta^m = 1$ whose image in the residue field is $u$. Thus reduction restricts to a bijection from $\mu_m(A)$ onto $\mu_m$ of the residue field. No completeness or henselianness hypothesis appears; the algebraic closedness of $K$ is what supplies the roots of unity to be lifted.
--
--   This is the statement that, away from the residual characteristic, $m$-th roots of unity of a valuation ring of an algebraically closed field are determined by, and realise, those of the residue field — a Teichmüller-style lifting statement for $\mu_m$. It is used in the analysis of semistable models and of the toric part of Néron models of modular curves, where characters and node units must be lifted from the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_residue_injOn_pow_eq_one_and_exists_residue_eq_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.residue_injOn_pow_eq_one_and_exists_residue_eq_of_isAlgClosed
    (K : Type*) [Field K] [IsAlgClosed K] (A : ValuationSubring K)
    (m : ℕ) (hm : (m : ResidueField ↥A) ≠ 0) :
    (∀ ζ₁ ζ₂ : ↥A, ζ₁ ^ m = 1 → ζ₂ ^ m = 1 → residue ↥A ζ₁ = residue ↥A ζ₂ → ζ₁ = ζ₂) ∧
    (∀ u : ResidueField ↥A, u ^ m = 1 → ∃ ζ : ↥A, ζ ^ m = 1 ∧ residue ↥A ζ = u) := by sorry
