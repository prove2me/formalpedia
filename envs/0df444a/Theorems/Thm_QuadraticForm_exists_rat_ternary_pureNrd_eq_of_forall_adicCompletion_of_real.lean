-- Prove2me | Theorems.Thm_QuadraticForm_exists_rat_ternary_pureNrd_eq_of_forall_adicCompletion_of_real
-- name    : QuadraticForm.exists_rat_ternary_pureNrd_eq_of_forall_adicCompletion_of_real
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/d4f4e483-e341-530e-95d0-2c531ca0e084
-- title:
--   Local–global principle for the ternary form -ax²-by²+abz²
-- statement:
--   Let $a,b,c$ be nonzero rational numbers. Assume first that for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$ there exist $x,y,z$ in the $v$-adic completion $\mathbb{Q}_v$ of $\mathbb{Q}$ with $-ax^2-by^2+abz^2=c$, the coefficients $a$, $b$ and $c$ being taken as images under the structure map $\mathbb{Q}\to\mathbb{Q}_v$; assume second that there exist real numbers $x,y,z$ with $-ax^2-by^2+abz^2=c$, the coefficients again being taken as images under $\mathbb{Q}\to\mathbb{R}$. The conclusion is that there exist rational $x,y,z$ with $-ax^2-by^2+abz^2=c$. Thus solvability of this single inhomogeneous ternary equation over every finite completion of $\mathbb{Q}$ together with solvability over $\mathbb{R}$ forces solvability over $\mathbb{Q}$. Note that $c$ is required to be nonzero, so the isotropy case $c=0$ is not covered; no condition beyond nonvanishing is imposed on $a$ and $b$.
--
--   This is the Hasse–Minkowski local–global principle in the special shape needed for quaternion algebras: $-ax^2-by^2+abz^2$ is the reduced norm restricted to the pure quaternions of $\left(\frac{a,b}{\mathbb{Q}}\right)$, so the statement says that a nonzero rational number represented by that form over $\mathbb{R}$ and over every $\mathbb{Q}_v$ is represented over $\mathbb{Q}$. It is used to produce rational pure quaternions of prescribed reduced norm, in particular elements with prescribed square in definite and indefinite quaternion algebras ramified at a given set of places, as in the construction of maximal orders and of the Čerednik–Drinfel'd setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuadraticForm_exists_rat_ternary_pureNrd_eq_of_forall_adicCompletion_of_real.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem QuadraticForm.exists_rat_ternary_pureNrd_eq_of_forall_adicCompletion_of_real
    (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (c : ℚ) (hc : c ≠ 0)
    (hv : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
      ∃ x y z : v.adicCompletion ℚ,
        -(algebraMap ℚ (v.adicCompletion ℚ) a) * x ^ 2 - (algebraMap ℚ (v.adicCompletion ℚ) b) * y ^ 2
          + (algebraMap ℚ (v.adicCompletion ℚ) a) * (algebraMap ℚ (v.adicCompletion ℚ) b) * z ^ 2
          = algebraMap ℚ (v.adicCompletion ℚ) c)
    (hR : ∃ x y z : ℝ, -(algebraMap ℚ ℝ a) * x ^ 2 - (algebraMap ℚ ℝ b) * y ^ 2
        + (algebraMap ℚ ℝ a) * (algebraMap ℚ ℝ b) * z ^ 2 = algebraMap ℚ ℝ c) :
    ∃ x y z : ℚ, -a * x ^ 2 - b * y ^ 2 + a * b * z ^ 2 = c := by sorry
