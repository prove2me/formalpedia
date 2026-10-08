-- Prove2me | Theorems.Thm_TalagrandConc_QPoints_eq_3_1_6
-- name    : TalagrandConc.QPoints.eq_3_1_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:41:20.39638+00:00
-- url     : https://prove2.me/theorems/ba2cf2dc-ebbe-4825-8296-8fb45586a22a
-- title:
--   Eq. (3.1.6) — $f(A,(x,\omega))\le 1+f(B,x)$ and $f(A,(x,\omega))\le f(C,x)$
-- statement:
--   Let $q\ge2$, let $A_1,\dots,A_q\subseteq\Omega^{N+1}$, and for $\omega\in\Omega$ let $A_i(\omega)=\{x\in\Omega^N:(x,\omega)\in A_i\}$ be the section of $A_i$ and $B_i=\{x:\exists\omega',(x,\omega')\in A_i\}$ its projection on $\Omega^N$. Then for all $x\in\Omega^N$ and $\omega\in\Omega$, with $f$ the $q$-point control of (3.1.1),
--   $$f(A_1,\dots,A_q,(x,\omega))\le 1+f(B_1,\dots,B_q,x),$$
--   and, for every $j\le q$,
--   $$f(A_1,\dots,A_q,(x,\omega))\le f(C_1,\dots,C_q,x),\qquad C_i=B_i\ (i\ne j),\quad C_j=A_j(\omega).$$
--
--   These are the two basic observations of the induction step in the proof of Theorem 3.1.1: the last coordinate $\omega$ is either given up (costing one coordinate) or captured by a point of $A_j$ whose last coordinate is $\omega$.
--
--   **Formalization Note** $(x,\omega)$ is `Fin.snoc x ω`; $f$ is $\mathbb N\cup\{+\infty\}$-valued with $1+\infty=\infty$.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), pp. 113–114, Eq. (3.1.6) and the display following it

import Mathlib
import Definitions.Def_TalagrandConc_QPoints_Basic

namespace TalagrandConc.QPoints

/-- The two observations (3.1.6) of the induction step of Theorem 3.1.1: with
`B i` the projection of `A i ⊆ Ω^{N+1}` on `Ω^N` and `A i (ω)` its section,
`f(A, (x, ω)) ≤ 1 + f(B, x)`, and for each `j`, `f(A, (x, ω)) ≤ f(C, x)` where
`C i = B i` for `i ≠ j` and `C j = A j (ω)`. -/
theorem eq_3_1_6 {Ω : Type*} {N q : ℕ} (hq : 2 ≤ q) (A : Fin q → Set (Fin (N + 1) → Ω))
    (x : Fin N → Ω) (ω : Ω) :
    qDist A (Fin.snoc x ω : Fin (N + 1) → Ω) ≤ 1 + qDist (fun i => projLast (A i)) x ∧
      ∀ j : Fin q, qDist A (Fin.snoc x ω : Fin (N + 1) → Ω) ≤
        qDist (Function.update (fun i => projLast (A i)) j (sliceAt (A j) ω)) x := by sorry

end TalagrandConc.QPoints
