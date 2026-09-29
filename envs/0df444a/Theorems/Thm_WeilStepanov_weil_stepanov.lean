-- Prove2me | Theorems.Thm_WeilStepanov_weil_stepanov
-- name    : WeilStepanov.weil_stepanov
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T09:00:14.439007+00:00
-- url     : https://prove2.me/theorems/1197b8fa-5718-40f9-80bd-6c22516ecc8d
-- title:
--   The Weil bound for hyperelliptic curves via Stepanov's method
-- statement:
--   **The Weil bound for hyperelliptic curves, by Stepanov's elementary method.**
--
--   Let $F$ be a finite field with $q = \#F$ odd, and let $f \in F[X]$ be a polynomial of degree
--   $m \ge 1$ with $f(0) \ne 0$ which is **not a square** in $\overline{F}[X]$. Write
--
--   $$N = \#\{(x,y) \in F \times F : y^2 = f(x)\}$$
--
--   for the number of affine points on the hyperelliptic curve $y^2 = f(x)$. Then $N$ deviates from
--   the trivial main term $q$ by at most $O_m(\sqrt q)$; explicitly, whenever $q \ge 16m^2$,
--
--   $$\bigl| N - q \bigr| \;\le\; 8\,m\,\bigl(\lfloor \sqrt q \rfloor + 1\bigr).$$
--
--   Fibring over $x$ and counting solutions of $y^2 = f(x)$ with the quadratic character $\chi$ (a
--   point $x$ contributes $1 + \chi(f(x))$ solutions) turns the estimate into a **character sum
--   bound**, $N - q = \sum_{x \in F} \chi(f(x))$, so the theorem is equivalently the statement that
--   this character sum exhibits square-root cancellation.
--
--   This is the special case of the Hasse–Weil bound that Stepanov proved by an elementary
--   argument, avoiding the Riemann hypothesis for curves over finite fields and the machinery of
--   algebraic geometry. The method constructs an auxiliary polynomial vanishing to high order at
--   the points of interest, and bounds the number of such points by a degree count. The squarefree
--   hypothesis is essential: if $f$ were a square then $\chi(f(x))$ would be constant and no
--   cancellation could occur.
--
--   **Formalization note.** The point count is written directly as
--   `Nat.card {p : F × F // p.2 ^ 2 = f.eval p.1}`, the non-squareness hypothesis is stated over
--   `AlgebraicClosure F`, and $\lfloor\sqrt q\rfloor$ is Lean's `Nat.sqrt`.
-- source:
--   S. A. Stepanov, *On the number of points of a hyperelliptic curve over a prime field* (1969); see also G. Harcos, *Elementary proof of the Weil bound*, and W. M. Schmidt, *Equations over Finite Fields: An Elementary Approach*. Lean proof extracted from `Salt/Weil/` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace WeilStepanov

open Polynomial in
theorem weil_stepanov {F : Type*} [Field F] [Fintype F] (f : Polynomial F)
    (hqodd : Odd (Fintype.card F)) (hm : 1 ≤ f.natDegree) (hf0 : f.coeff 0 ≠ 0)
    (hns : ¬ ∃ g : (AlgebraicClosure F)[X],
      f.map (algebraMap F (AlgebraicClosure F)) = g ^ 2)
    (hq : 16 * f.natDegree ^ 2 ≤ Fintype.card F) :
    |(Nat.card {p : F × F // p.2 ^ 2 = f.eval p.1} : ℤ) - Fintype.card F|
      ≤ 8 * f.natDegree * (Nat.sqrt (Fintype.card F) + 1) := by sorry

end WeilStepanov
