-- Prove2me | Theorems.Thm_ToddKK14_Diameter_small_cases
-- name    : ToddKK14.Diameter.small_cases
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:45:37.184924+00:00
-- url     : https://prove2.me/theorems/e9f77b34-42df-4419-9442-030f48c92bfb
-- title:
--   §2, p. 3, proof of Theorem 1 — the ten remaining cases d = 4…7 satisfy the recursion of Lemma 1
-- statement:
--   Write $T(d,n)=\lfloor (n-d)^{\log_2 d}\rfloor$ for the Todd bound. For each of the ten pairs
--
--   $$
--   d=4,\ 8\le n\le 11;\qquad d=5,\ 10\le n\le 12;\qquad d=6,\ 12\le n\le 13;\qquad d=7,\ n=14,
--   $$
--
--   the bound satisfies the recursion of Lemma 1:
--
--   $$
--   T(d-1,\,n-1) + 2\,T(d,\lfloor n/2\rfloor) + 2 \;\le\; T(d,n).
--   $$
--
--   These are the cases of the induction proving Theorem 1 that are covered neither by $n<2d$ nor by the general step ($d\ge 4$, $n-d\ge 8$). The paper says they "can be checked easily using the lemma, the equation $\Delta(d,d)=0$, and the equations $\Delta(5,6)=\Delta(4,5)=\Delta(3,4)=\Delta(2,3)=1$". In all ten cases $\lfloor n/2\rfloor\in\{d,d+1\}$, and $T(d,d)=0$, $T(d,d+1)=1$ are exactly those equations; with the induction hypothesis $\Delta(d-1,n-1)\le T(d-1,n-1)$ and Lemma 1, the displayed inequality gives $\Delta(d,n)\le T(d,n)$.
--
--   **Formalization Note** $T$ is `toddBound`, with `Real.logb 2` and the real power; $n-1$, $d-1$ and $\lfloor n/2\rfloor$ (`n / 2`) are natural-number operations, exact here since $n\ge 8$ and $d\ge 4$. The list of cases is exactly the paper's.
-- source:
--   Todd, An improved Kalai-Kleitman bound for the diameter of a polyhedron, arXiv:1402.3579v2, p. 3, §2, proof of Theorem 1, sentences "The remaining cases are …" and "All these cases can be checked easily …"

import Mathlib
import Definitions.Def_ToddKK14_Diameter_Bound

namespace ToddKK14.Diameter

/-- Todd (2014), p. 3, proof of Theorem 1: "The remaining cases are d = 4, 8 ≤ n ≤ 11; d = 5,
10 ≤ n ≤ 12; d = 6, 12 ≤ n ≤ 13; and d = 7, n = 14. All these cases can be checked easily using the
lemma, the equation ∆(d, d) = 0, and the equations ∆(5, 6) = ∆(4, 5) = ∆(3, 4) = ∆(2, 3) = 1."
In each of these ten cases the bound `⌊(n − d)^{log₂ d}⌋` satisfies the recursion of Lemma 1:
`toddBound (d-1) (n-1) + 2 * toddBound d ⌊n/2⌋ + 2 ≤ toddBound d n`. -/
theorem small_cases (d n : ℕ)
    (h : (d = 4 ∧ 8 ≤ n ∧ n ≤ 11) ∨ (d = 5 ∧ 10 ≤ n ∧ n ≤ 12) ∨ (d = 6 ∧ 12 ≤ n ∧ n ≤ 13) ∨
      (d = 7 ∧ n = 14)) :
    toddBound (d - 1) (n - 1) + 2 * toddBound d (n / 2) + 2 ≤ toddBound d n := by sorry

end ToddKK14.Diameter
