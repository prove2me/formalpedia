-- Prove2me | Theorems.Thm_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split
-- name    : QuadraticForm.exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/5ffe2e07-cfd5-55c1-ada2-ae2e4564c456
-- title:
--   Pure norm form represents c at a non-split place
-- statement:
--   Let $a,b$ be nonzero rationals and let $v$ be a point of the height-one spectrum of the ring of integers of $\mathbb{Q}$, i.e. a finite place of $\mathbb{Q}$, with completion $\mathbb{Q}_v$ denoted `v.adicCompletion ℚ`. Assume that the quaternion algebra over $\mathbb{Q}_v$ with parameters $(a,0,b)$ — that is, the algebra with generators $i,j$ satisfying $i^2 = a$, $j^2 = b$ (the images of $a$ and $b$ under $\mathbb{Q} \to \mathbb{Q}_v$ being used) — admits no $\mathbb{Q}_v$-algebra isomorphism onto the $2\times 2$ matrix algebra $M_2(\mathbb{Q}_v)$; the hypothesis is stated as emptiness of the type of such isomorphisms. Let $c \in \mathbb{Q}_v$ be such that $-c$ is not a square in $\mathbb{Q}_v$ (in particular $c \neq 0$, since $0$ is a square). The conclusion asserts the existence of $x,y,z \in \mathbb{Q}_v$ with
--   $$-a x^2 - b y^2 + ab z^2 = c,$$
--   the coefficients again being the images of $a$, $b$ and $ab$ in $\mathbb{Q}_v$.
--
--   The form $-ax^2-by^2+abz^2$ is the reduced norm restricted to the pure quaternions of $\left(\frac{a,b}{\mathbb{Q}_v}\right)$, so the statement says that over a non-split, i.e. division, local quaternion algebra every quadratic extension $\mathbb{Q}_v(\sqrt{-c})$ is realised by a pure quaternion of square $-c$. It is used in the construction of elements of prescribed reduced norm and of square $-c$ in quaternion orders, for instance in the Čerednik–Drinfeld input [`CerednikDrinfeld.QM.exists_sq_eq_neg_disc_and_forall_conj_mem_of_isMaximalOrder`](thm.html#CerednikDrinfeld.QM.exists_sq_eq_neg_disc_and_forall_conj_mem_of_isMaximalOrder) and in the existence results for definite and indefinite quaternion algebras ramified at a prescribed set of places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem QuadraticForm.exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split
    (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (hv : ¬ Nonempty (QuaternionAlgebra (v.adicCompletion ℚ)
        (algebraMap ℚ (v.adicCompletion ℚ) a) 0 (algebraMap ℚ (v.adicCompletion ℚ) b)
          ≃ₐ[v.adicCompletion ℚ] Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (c : v.adicCompletion ℚ) (hc : ¬ IsSquare (-c)) :
    ∃ x y z : v.adicCompletion ℚ,
      -(algebraMap ℚ (v.adicCompletion ℚ) a) * x ^ 2 - (algebraMap ℚ (v.adicCompletion ℚ) b) * y ^ 2
        + (algebraMap ℚ (v.adicCompletion ℚ) a) * (algebraMap ℚ (v.adicCompletion ℚ) b) * z ^ 2 = c := by sorry
