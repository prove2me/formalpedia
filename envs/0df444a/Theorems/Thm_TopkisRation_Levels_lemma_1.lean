-- Prove2me | Theorems.Thm_TopkisRation_Levels_lemma_1
-- name    : TopkisRation.Levels.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:46:54.793436+00:00
-- url     : https://prove2.me/theorems/d89f076e-89aa-44fb-9918-bb668db0de7c
-- title:
--   Lemma 1, p. 163 — minimizing a convex function over one block of variables leaves a convex function
-- statement:
--   Let $E$ and $F$ be real vector spaces, $A\subseteq E\times F$ a convex set and $\varphi:A\to\mathbb R$ a convex function. Suppose that for every $u\in E$ the values $\varphi(u,w)$, $(u,w)\in A$, are bounded below. Then the function
--
--   $$
--   \psi(u)=\inf_{w:\,(u,w)\in A}\varphi(u,w)
--   $$
--
--   is convex on the projection $\{u:\ \exists w,\ (u,w)\in A\}$.
--
--   In the paper this well-known fact gives convexity of $f_t$ and $g_t$ from the recursion (1): the infimum over the decision $u$ of a jointly convex function of the state and the decision is convex in the state.
--
--   **Formalization Note.** The paper calls the function $f$ and the infimum $g$; they are renamed $\varphi$ and $\psi$ here to avoid a clash with the model's $f_t$, $g_t$. The boundedness hypothesis is added: the paper's infimum may be $-\infty$, which is not a real number, and a real `sInf` of a set unbounded below is the junk value $0$, for which the conclusion can fail. With the hypothesis every infimum is the real number the paper means.
-- source:
--   Topkis, Optimal ordering and rationing policies in a nonstationary dynamic inventory model with n demand classes, Management Science 15 (1968), p. 163, Lemma 1

import Mathlib

namespace TopkisRation.Levels

theorem lemma_1 {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (A : Set (E × F)) (hA : Convex ℝ A) (φ : E × F → ℝ) (hφ : ConvexOn ℝ A φ)
    (hbdd : ∀ u, BddBelow (φ '' {q | q ∈ A ∧ q.1 = u})) :
    ConvexOn ℝ (Prod.fst '' A) (fun u => sInf (φ '' {q | q ∈ A ∧ q.1 = u})) := by sorry

end TopkisRation.Levels
