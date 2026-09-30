-- Prove2me | Theorems.Thm_TranscendenceTheory_finite_set_subgroup_obstruction_exclusion
-- name    : TranscendenceTheory.finite_set_subgroup_obstruction_exclusion
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-08T15:36:13.250286+00:00
-- url     : https://prove2.me/theorems/2edf044e-5669-4ed1-98d5-2b791ba3f91e
-- title:
--   Finite-set size bounds exclude subgroup multiplicity obstructions
-- statement:
--   Let $A$ be a module over a ring $R$, let $\Lambda$ be a submodule, and let $X\subset A$ be finite. For a submodule $K$, write $q_K:A\to A/K$ for the quotient map. Suppose $C>0$, $m,n\ge1$, $T\ge0$ are integers except for the real constant $C$, and
--
--   $$3Cmn^2<T|X|,\qquad 3Cn^2<T|q_\Lambda(X)|.$$
--
--   Let $K$ be any submodule and $a,b$ nonnegative integers with $b\le2$. Assume either $a=1$ and $K=\{0\}$, or $a=0$ and $K\subseteq\Lambda$. Then
--
--   $$Cm^an^b<\big(\lfloor T/3\rfloor+1\big)|q_K(X)|.$$
--
--   Thus no such submodule and degree exponents can satisfy the reverse weak inequality. No finiteness assumption is placed on $K$ or $\Lambda$, and $X$ need not contain zero. The quotient images are finite because $X$ is finite. The statement applies in particular to additive subgroups of $\mathbb C$, viewed as $\mathbb Z$-submodules.
-- source:
--   Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2-A.3 and Lemma A.1(b), https://doi.org/10.1017/S001309152610145X. This derived module-theoretic and numerical lemma proves the quotient-count comparison and obstruction exclusion used in the finite-set specialization. It makes the two subgroup profiles explicit and uses U=floor(T/3). It does not assert the multiplicity theorem or the classification of algebraic subgroups.

import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic

theorem TranscendenceTheory.finite_set_subgroup_obstruction_exclusion
    (R A : Type*) [Ring R] [AddCommGroup A] [Module R A]
    (Λ : Submodule R A) (X : Finset A)
    (C : ℝ) (hC : 0 < C) (m n T : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hfirst : 3 * C * (m : ℝ) * (n : ℝ) ^ 2 < (T : ℝ) * X.card)
    (hsecond : 3 * C * (n : ℝ) ^ 2 <
      (T : ℝ) * (Λ.mkQ '' (X : Set A)).ncard)
    (K : Submodule R A) (a b : ℕ)
    (hprofile : (a = 1 ∧ K = ⊥) ∨ (a = 0 ∧ K ≤ Λ)) (hb : b ≤ 2) :
    C * (m : ℝ) ^ a * (n : ℝ) ^ b <
      ((T / 3 + 1 : ℕ) : ℝ) * (K.mkQ '' (X : Set A)).ncard := by sorry
