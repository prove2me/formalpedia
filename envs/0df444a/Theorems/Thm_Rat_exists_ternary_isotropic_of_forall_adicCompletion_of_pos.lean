-- Prove2me | Theorems.Thm_Rat_exists_ternary_isotropic_of_forall_adicCompletion_of_pos
-- name    : Rat.exists_ternary_isotropic_of_forall_adicCompletion_of_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/c5277d28-262d-5c5c-8da8-f87246c03785
-- title:
--   Legendre's theorem: local–global isotropy for z²-ax²-by²
-- statement:
--   Let $a$ and $b$ be nonzero rational numbers. Assume first a local hypothesis at the finite places: for every $v$ in the height-one spectrum of the ring of integers of $\mathbb{Q}$, there exist elements $z, x, y$ of the $v$-adic completion $\mathbb{Q}_v$ of $\mathbb{Q}$, not all three equal to zero, such that $z^2 - a x^2 - b y^2 = 0$, the coefficients $a$ and $b$ being mapped into $\mathbb{Q}_v$ along the structure map $\mathbb{Q} \to \mathbb{Q}_v$. Assume second the real condition that $0 < a$ or $0 < b$. The conclusion is that there exist rational numbers $z, x, y$, not all three equal to zero, with $z^2 - a x^2 - b y^2 = 0$; that is, the ternary quadratic form $z^2 - a x^2 - b y^2$ is isotropic over $\mathbb{Q}$. Note that the negation in the nontriviality clause is of the conjunction $z = 0 \wedge x = 0 \wedge y = 0$, so it asserts exactly that the triple $(z,x,y)$ is not the zero triple.
--
--   This is Legendre's theorem, the ternary case $n = 3$ of the Hasse–Minkowski theorem over $\mathbb{Q}$, with the archimedean local condition written out concretely as $0 < a \vee 0 < b$. It is used in the construction and recognition of definite quaternion algebras over $\mathbb{Q}$ with prescribed ramification, namely by [`QuaternionAlgebra.isDefiniteRamifiedExactlyAt_of_split_away_of_forall_isUnit`](thm.html#QuaternionAlgebra.isDefiniteRamifiedExactlyAt_of_split_away_of_forall_isUnit) and [`QuaternionAlgebra.nonempty_algEquiv_of_isDefiniteRamifiedExactlyAt_of_prime`](thm.html#QuaternionAlgebra.nonempty_algEquiv_of_isDefiniteRamifiedExactlyAt_of_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rat_exists_ternary_isotropic_of_forall_adicCompletion_of_pos.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsDedekindDomain NumberField

theorem Rat.exists_ternary_isotropic_of_forall_adicCompletion_of_pos
    (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hv : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
      ∃ z x y : v.adicCompletion ℚ, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
        z ^ 2 - (algebraMap ℚ (v.adicCompletion ℚ) a) * x ^ 2
          - (algebraMap ℚ (v.adicCompletion ℚ) b) * y ^ 2 = 0)
    (hR : 0 < a ∨ 0 < b) :
    ∃ z x y : ℚ, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0 := by sorry
