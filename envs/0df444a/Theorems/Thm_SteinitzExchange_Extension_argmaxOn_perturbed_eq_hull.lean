-- Prove2me | Theorems.Thm_SteinitzExchange_Extension_argmaxOn_perturbed_eq_hull
-- name    : SteinitzExchange.Extension.argmaxOn_perturbed_eq_hull
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T16:44:11.369814+00:00
-- url     : https://prove2.me/theorems/17853cd0-8571-4d05-9f61-95d1c63055b0
-- title:
--   Lemma 4.1+4.2 — the maximizers of $\hat g[p]$ over $\overline B$ are $\overline{\operatorname{argmax}(g[p])}$
-- statement:
--   Let $B\subseteq \mathbb Z^V$ be a nonempty finite set, $g:B\to\mathbb R$ any function, and let $\hat g$ be its concave closure on $\overline B$ (Murota 1996, Eq. (4.2)). For a linear perturbation $p\in\mathbb R^V$ write
--
--   $$\hat g[p](b) = \hat g(b) + \langle p, b\rangle \quad (b\in\overline B), \qquad g[p](x) = g(x) + \langle p, x\rangle \quad (x\in B).$$
--
--   Then the maximizers of $\hat g[p]$ taken over $\overline B$ are exactly the convex hull of the maximizers of $g[p]$ taken over $B$:
--
--   $$\operatorname{argmax}(\hat g[p]) = \overline{\operatorname{argmax}(g[p])}.$$
--
--   **Why this holds.** Murota's Lemma 4.1 identifies the maximizers of the concave closure itself, $\operatorname{argmax}(\hat g) = \overline{\operatorname{argmax}(g)}$, and Lemma 4.2 identifies the perturbed closure, $\hat g[p] = \hat g + \langle p,\cdot\rangle$. Maximizing a function and maximizing that same function plus a linear functional on a fixed convex set select the same points, because a linear functional is constant-shifted and its level sets are the same: for a concave function on a polytope the set of maximizers of $\hat g + \langle p,\cdot\rangle$ is the face of $\operatorname{argmax}(\hat g)$ exposed by $p$, and every exposed face of a polytope is a polytope. This lemma is the standard step used to pass from the discrete function $g[p]$ on the lattice points $B$ to the concave function $\hat g[p]$ on $\overline B$.
--
--   **Formalization Note.** $\hat g$ and $\hat g[p]$ are total functions on $\mathbb R^V$ but are evaluated only on $\overline B$, where the defining infimum is bounded below, so no upper semicontinuity is needed. The left-hand side is `argmaxOn (hull B) (fun b => concaveClosure B g b + pairing p b)`, the set of maximizers over $\overline B$; the right-hand side is the convex hull of the finite maximizer set of $g[p]$ on $B$.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 285, Lemma 4.1 (Eq. (4.6)) together with p. 285, Lemma 4.2 (Eq. (4.7))

import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Extension_Exchange
import Definitions.Def_SteinitzExchange_Extension_ConcaveClosure

namespace SteinitzExchange.Extension

/-- Murota 1996, p. 285, Lemma 4.1 together with p. 285, Lemma 4.2 (Eq. (4.7)). For any `g : B → ℝ` on a nonempty
finite `B ⊆ ℤ^V` and every `p : V → ℝ`, the maximizers over `B̄` of the perturbed concave closure
`ĝ[p] = (ĝ + ⟨p, ·⟩)` are exactly `conv(argmax(g[p]))`, i.e.
`argmax(ĝ[p]) = conv(argmax(g[p]))` where `g[p](x) = g(x) + ⟨p, x⟩` on `B`.

This is the identity that transfers maximization about the lattice function `g[p] : B → ℝ` to the
concave function `ĝ[p] : B̄ → ℝ`; by Thm 4.4 it turns an integral base set `argmax(g[p])` into the
integral base polytope `conv(argmax(g[p]))` required by the Extension Theorem (Thm 4.6). -/
theorem argmaxOn_perturbed_eq_hull {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : B.Nonempty) (g : (V → ℤ) → ℝ) (p : V → ℝ) :
    argmaxOn (hull B) (fun b => concaveClosure B g b + pairing p b) = hull (argmaxB B (perturb g p)) := by sorry

end SteinitzExchange.Extension
