-- Prove2me | Theorems.Thm_VaryingConstants_buckingham_pi
-- name    : VaryingConstants.buckingham_pi
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-02T03:30:37.374014+00:00
-- url     : https://prove2.me/theorems/e8b2d770-c31f-4b8a-8da2-ddedf24b3bc5
-- title:
--   Buckingham $\pi$ theorem for physical constants (goal)
-- statement:
--   Let $D\in\mathbb R^{n\times d}$ be the dimension matrix of $n$ constants with respect to $d$ base units, and put $k=n-\operatorname{rank}D$. Then there exist exponent vectors $a^{(1)},\dots,a^{(k)}\in\mathbb R^n$ such that
--
--   1. each $a^{(l)}$ is dimensionless: $\sum_i a^{(l)}_iD_{ij}=0$ for all $j$;
--   2. $a^{(1)},\dots,a^{(k)}$ are linearly independent;
--   3. for every unit-invariant observable $f:\mathbb R^n\to\mathbb R$ there is a function $F:\mathbb R^k\to\mathbb R$ with
--   $$ f(x)=F\big(\pi_1(x),\dots,\pi_k(x)\big),\qquad \pi_l(x)=\prod_{i=1}^n x_i^{a^{(l)}_i}, $$
--   for every positive configuration $x\in\mathbb R^n_{>0}$.
--
--   Every quantity that does not depend on the choice of units is a function of $n-\operatorname{rank}D$ independent dimensionless combinations of the constants. This is the mathematical statement behind Uzan's §2.1: the physically meaningful parameters are the dimensionless numbers (such as $\alpha_{\rm EM}$ or $m_p/m_e$), and only their variation is observable.
--
--   **Formalization Note** No regularity of $f$ or $F$ is required; $f$ is only constrained on positive configurations.
-- source:
--   J.-P. Uzan, "Varying Constants, Gravitation and Cosmology", Living Rev. Relativity 14 (2011) 2, http://www.livingreviews.org/lrr-2011-2, §2.1.1–2.1.2, pp. 14–17 (dimensionless combinations of constants, natural units, "only the variation of dimensionless constants can be measured"); classical statement: E. Buckingham, Phys. Rev. 4 (1914) 345, https://doi.org/10.1103/PhysRev.4.345.

import Mathlib
import Definitions.Def_VaryingConstants_units

namespace VaryingConstants

theorem buckingham_pi {n d : ℕ} (D : Matrix (Fin n) (Fin d) ℝ) :
    ∃ a : Fin (n - D.rank) → (Fin n → ℝ),
      (∀ l, a l ∈ dimensionlessExponents D) ∧ LinearIndependent ℝ a ∧
      ∀ f : (Fin n → ℝ) → ℝ, IsUnitInvariant D f →
        ∃ F : (Fin (n - D.rank) → ℝ) → ℝ,
          ∀ x : Fin n → ℝ, IsPositive x → f x = F (fun l => powerMonomial (a l) x) := by sorry

end VaryingConstants
