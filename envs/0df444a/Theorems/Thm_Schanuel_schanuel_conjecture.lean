-- Prove2me | Theorems.Thm_Schanuel_schanuel_conjecture
-- name    : Schanuel.schanuel_conjecture
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T17:28:53.41353+00:00
-- url     : https://prove2.me/theorems/604f4a66-9bc5-4f30-8d7f-89c744b5d1b1
-- title:
--   Schanuel's conjecture
-- statement:
--   **Schanuel's conjecture.** Let $n \ge 0$ and let $z_1, \dots, z_n$ be complex numbers that are linearly independent over $\mathbb{Q}$, i.e. the only rationals $q_1,\dots,q_n$ with $\sum_i q_i z_i = 0$ are $q_1 = \dots = q_n = 0$. Then the field extension of $\mathbb{Q}$ generated inside $\mathbb{C}$ by the $2n$ numbers $z_1,\dots,z_n, e^{z_1},\dots,e^{z_n}$ has transcendence degree at least $n$ over $\mathbb{Q}$:
--
--   $$\operatorname{trdeg}_{\mathbb{Q}} \mathbb{Q}\bigl(z_1,\dots,z_n, e^{z_1},\dots,e^{z_n}\bigr) \;\ge\; n.$$
--
--   The conjecture is due to Stephen Schanuel and was first published by Lang in 1966. It contains the Lindemann–Weierstrass theorem (the case of algebraic $z_i$) and Baker's theorem (the case where all $e^{z_i}$ are algebraic) as special cases, and implies many open statements, among them the algebraic independence of $e$ and $\pi$.
-- source:
--   S. Lang, Introduction to Transcendental Numbers, Addison-Wesley, 1966, Chapter III; see also https://en.wikipedia.org/wiki/Schanuel%27s_conjecture

import Mathlib

namespace Schanuel
theorem schanuel_conjecture (n : ℕ) (z : Fin n → ℂ) (hz : LinearIndependent ℚ z) :
    (n : Cardinal) ≤ Algebra.trdeg ℚ
      (IntermediateField.adjoin ℚ (Set.range z ∪ Set.range (Complex.exp ∘ z))) := by sorry
end Schanuel
