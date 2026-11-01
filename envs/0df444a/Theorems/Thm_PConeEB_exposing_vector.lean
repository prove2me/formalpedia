-- Prove2me | Theorems.Thm_PConeEB_exposing_vector
-- name    : PConeEB.exposing_vector
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:34:18.07454+00:00
-- url     : https://prove2.me/theorems/6ff0d488-18a6-47ee-a77f-2fcd3df85b5e
-- title:
--   Proof of Theorem 4.3 — the exposing vector $z$
-- statement:
--   Let $n\ge2$, $p,q\in(1,\infty)$ with $\frac1p+\frac1q=1$, $\mathcal L\subseteq\mathbb R^{n+1}$ a subspace and $a\in\mathbb R^{n+1}$. Suppose that $(\mathcal L+a)\cap\mathcal K_p^{n+1}$ is nonempty, does not meet $\operatorname{ri}\mathcal K_p^{n+1}$, and is not $\{0\}$. Then there is
--   $$
--   z\in\partial\mathcal K_q^{n+1}\setminus\{0\}\quad\text{with}\quad z\in\mathcal L^\perp\cap\{a\}^\perp,
--   $$
--   and for this $z$,
--   $$
--   \mathcal K_p^{n+1}\cap(\mathcal L+a)=(\mathcal K_p^{n+1}\cap\{z\}^\perp)\cap(\mathcal L+a).
--   $$
--
--   This is the single facial reduction step of the mission: outside item (i) of Theorem 4.3, the feasible region lies in the face exposed by $z$.
--
--   Differences from the source:
--   - reading: the page takes z from the chain of Proposition 2.2 and states F₂ = F_z with z ∈ ∂K_q \ {0} → the existence of z is stated directly, with K ∩ (L + a) = (K ∩ {z}^⊥) ∩ (L + a), which is item (iii) of Proposition 2.2 for this z; reason: the mission does not model chains of faces (paper.md D1); the conclusion is what the page draws from them
--   - encoding: ℝ^{n+1}, x₀, x̄, ‖x̄‖_p, ∂ → RR n = EuclideanSpace ℝ (Fin (n + 1)), x 0, x i.succ for i : Fin n, pNorm with real rpow, frontier; reason: Lean conventions; same instances
-- source:
--   Lindstrom, Lourenço & Pong, Optimal error bounds in the absence of constraint qualifications, arXiv:2109.11729v4, proof of Theorem 4.3, p.29

import Mathlib
import Definitions.Def_PConeEB_affineSet
import Definitions.Def_PConeEB_hyperplane
import Definitions.Def_PConeEB_pCone

namespace PConeEB

/-- The exposing vector in the proof of Theorem 4.3: if `(L + a) ∩ K_p^{n+1}` is nonempty, misses
`ri K_p^{n+1}` and is not `{0}`, then there is `z ∈ ∂K_q^{n+1} \ {0}` in `L^⊥ ∩ {a}^⊥`, and the
feasible region is unchanged on replacing `K_p^{n+1}` by the face `K_p^{n+1} ∩ {z}^⊥`.
Lindstrom, Lourenço & Pong, arXiv:2109.11729v4, proof of Theorem 4.3, p.29. -/
theorem exposing_vector {n : ℕ} (hn : 2 ≤ n) {p q : ℝ} (hp : 1 < p)
    (hpq : 1 / p + 1 / q = 1) (L : Submodule ℝ (RR n)) (a : RR n)
    (hfeas : (affineSet L a ∩ pCone n p).Nonempty)
    (hri : affineSet L a ∩ intrinsicInterior ℝ (pCone n p) = ∅)
    (hne : affineSet L a ∩ pCone n p ≠ {0}) :
    ∃ z : RR n, z ∈ frontier (pCone n q) ∧ z ≠ 0 ∧ z ∈ Lᗮ ∧ inner ℝ z a = 0 ∧
      pCone n p ∩ affineSet L a = (pCone n p ∩ hyperplane z) ∩ affineSet L a := by sorry

end PConeEB
