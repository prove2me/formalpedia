-- Prove2me | Theorems.Thm_Tucker_exists_complementary_edge_cube
-- name    : Tucker.exists_complementary_edge_cube
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T09:37:16.76711+00:00
-- url     : https://prove2.me/theorems/a259b70f-a19e-4265-a66b-8f009674bb95
-- title:
--   Tucker's lemma — an antipodal boundary labelling of the cube's Kuhn triangulation has a complementary edge
-- statement:
--   **Statement.** Let $n \ge 0$ and $m \ge 1$, and label every integer point $x$ of the cube $[-m,m]^n$ by an integer $\ell(x) \in \{\pm1, \dots, \pm n\}$. Assume the labelling is antipodal on the boundary: $\ell(-x) = -\ell(x)$ whenever some coordinate satisfies $|x_a| = m$. Then there are two cube points $x, y$ with opposite labels, $\ell(x) + \ell(y) = 0$, that span an edge of the reflected Kuhn triangulation of the cube. Concretely, the two points satisfy all of the following:
--   - they lie in a common closed orthant: $x_i y_i \ge 0$ for every $i$;
--   - their absolute values are comparable: $|x_i| \le |y_i|$ for all $i$, or $|y_i| \le |x_i|$ for all $i$;
--   - they are at $\ell^\infty$-distance at most 1: $|x_i - y_i| \le 1$ for every $i$.
--
--   **Relation to the usual statement.** This is Tucker's lemma for one specific triangulation. The usual statement (Tucker 1946) concerns any triangulation of the $n$-ball that is antipodally symmetric on its boundary sphere, with vertex labels in $\{\pm1, \dots, \pm n\}$ forming an odd function on the boundary. Its conclusion is a *complementary edge*: a 1-simplex whose two vertices carry the same number with opposite signs.
--
--   The triangulation here is the reflected Kuhn (Freudenthal) triangulation of $[-m,m]^n$:
--   - its vertices are the integer points;
--   - its simplices are the sets of integer points that lie in one closed orthant, whose absolute values form a chain under the coordinatewise order, and whose coordinates differ by at most 1;
--   - it is antipodally symmetric.
--
--   Two points span an edge exactly when they satisfy the three conditions above. In Lean the labelling is a function on all of $\mathbb Z^n$, constrained only on the cube, and the label set is written as $\ell(x) \neq 0$ and $|\ell(x)| \le n$. For $n = 0$ the hypotheses cannot hold.
--
--   Tucker's lemma is the combinatorial counterpart of the Borsuk–Ulam theorem and gives a combinatorial proof of it (`BorsukUlam.exists_eq_neg`). Constructive, path-following proofs are due to Freund and Todd.
--
--   References:
--   - A. W. Tucker, *Some topological properties of disk and sphere*, Proc. First Canadian Math. Congress, Montreal 1945, University of Toronto Press (1946), pp. 285–309. This is a proceedings volume and has no DOI.
--   - R. M. Freund and M. J. Todd, *A constructive proof of Tucker's combinatorial lemma*, J. Combin. Theory Ser. A 30(3) (1981) 321–325, https://doi.org/10.1016/0097-3165(81)90027-3.
-- source:
--   Tucker, Some topological properties of disk and sphere, Proc. First Canadian Math. Congress, Montreal 1945, University of Toronto Press (1946) (proceedings volume, no DOI), pp. 285–309, Tucker's lemma, here for the reflected Kuhn triangulation of the cube [-m,m]^n, constructive proof: Freund, Todd, A constructive proof of Tucker's combinatorial lemma, J. Combin. Theory Ser. A 30(3) (1981) 321–325, https://doi.org/10.1016/0097-3165(81)90027-3

import Mathlib

namespace Tucker

theorem exists_complementary_edge_cube (n m : ℕ) (hm : 1 ≤ m) (lab : (Fin n → ℤ) → ℤ)
    (hlab : ∀ x : Fin n → ℤ, (∀ i, |x i| ≤ m) → lab x ≠ 0 ∧ |lab x| ≤ n)
    (hanti : ∀ x : Fin n → ℤ, (∀ i, |x i| ≤ m) → (∃ a, |x a| = m) → lab (-x) = -lab x) :
    ∃ x y : Fin n → ℤ, (∀ i, |x i| ≤ m) ∧ (∀ i, |y i| ≤ m) ∧
      (∀ i, 0 ≤ x i * y i) ∧ ((∀ i, |x i| ≤ |y i|) ∨ (∀ i, |y i| ≤ |x i|)) ∧
      (∀ i, |x i - y i| ≤ 1) ∧ lab x + lab y = 0 := by
  sorry

end Tucker
