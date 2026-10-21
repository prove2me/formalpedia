-- Prove2me | Theorems.Thm_UCConvexHull_OneUC_proposition_1
-- name    : UCConvexHull.OneUC.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:14:51.476642+00:00
-- url     : https://prove2.me/theorems/b890549e-dcb7-47d9-8163-1537390e80f3
-- title:
--   Proposition 1, pp. 16–17 — if σ_S(c) = D(c) for every c, the closed convex NLP set C is the closed convex hull of its mixed-integer restriction S
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R^m$ and suppose the NLP set $C=\{\,z\in\mathbb R^n : f(z)\le 0\,\}$ is closed and convex. Let $K\subseteq\{1,\dots,n\}$ and let $S=\{\,z\in C : z_k\in\mathbb Z,\ k\in K\,\}$ be the mixed-integer restriction of $C$. For $c\in\mathbb R^n$ write $\sigma_S(c)=\inf\{\,cz : z\in S\,\}$ and $D(c)=\sup_{\lambda\ge 0}\inf_{z\in\mathbb R^n}\{\,cz+\lambda f(z)\,\}$ for the Lagrangian dual, both in the extended reals. If
--
--   $$\sigma_S(c)=D(c)\qquad\text{for every } c\in\mathbb R^n,$$
--
--   then
--
--   $$C=\overline{\operatorname{conv}}(S),$$
--
--   the closure of the convex hull of $S$.
--
--   This is the duality characterization of the closed convex hull of a mixed-integer convex set that the paper uses to prove Lemma 1.
--
--   **Formalization Note.** "Closed convex NLP set" is read as: the set $C$ is convex and closed. Nothing is assumed about the component functions $f_i$. The weak-duality inequality $\sigma_C(c)\ge D(c)$ of (22) is part of the setting, not a hypothesis.
-- source:
--   Bacci, Frangioni, Gentile, Tavlaridis-Gyparakis, New MINLP Formulations for the Unit Commitment Problems with Ramping Constraints, manuscript submitted to Operations Research (PDF sha256 eee1c5a4…e224), pp. 16–17, Proposition 1, (22), (23)

import Mathlib
import Definitions.Def_UCConvexHull_OneUC_HullTools

namespace UCConvexHull.OneUC

/-- Proposition 1 (pp. 16–17): if `C = {f ≤ 0}` is closed and convex and its mixed-integer
restriction `S` satisfies `σ_S(c) = D(c)` for every `c`, then `C` is the closure of the convex hull
of `S`. -/
theorem proposition_1 {n m : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ)) (K : Finset (Fin n))
    (hconv : Convex ℝ (conSet f)) (hclosed : IsClosed (conSet f))
    (h23 : ∀ c : Fin n → ℝ, supportInf (miRestriction f K) c = lagDual f c) :
    conSet f = closure (convexHull ℝ (miRestriction f K)) := by sorry

end UCConvexHull.OneUC
