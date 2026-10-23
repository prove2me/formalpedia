-- Prove2me | Theorems.Thm_UniversalBarrier_NSC_theorem_2
-- name    : UniversalBarrier.NSC.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:48.847038+00:00
-- url     : https://prove2.me/theorems/853ba897-089f-4e93-b326-387feb55c7f0
-- title:
--   Theorem 2, p. 5 — the universal barrier of a proper convex domain in ℝⁿ is an n-self-concordant barrier
-- statement:
--   Let $n\ge1$ and let $K\subseteq\mathbb R^n$ be a proper convex domain: a convex set with non-empty interior that contains no line. Let
--   $$\varphi(x)=\log\mathrm{Vol}_n\bigl(K^\circ(x)\bigr),\qquad K^\circ(x)=\{y\in\mathbb R^n:\ y^{\mathsf T}(z-x)\le1\ \ \forall z\in K\},$$
--   be the universal barrier of $K$. Then $\varphi$ is an $n$-self-concordant barrier for $K$:
--   1. $\varphi(x)\to+\infty$ as $x\to\partial K$ within $\operatorname{int}(K)$;
--   2. $\varphi$ is convex and three times continuously differentiable on $\operatorname{int}(K)$, and for all $x\in\operatorname{int}(K)$ and $h\in\mathbb R^n$,
--   $$\bigl|D^3\varphi(x)[h,h,h]\bigr|\ \le\ 2\bigl(D^2\varphi(x)[h,h]\bigr)^{3/2};$$
--   3. for all $x\in\operatorname{int}(K)$ and $h\in\mathbb R^n$,
--   $$D\varphi(x)[h]\ \le\ \bigl(n\cdot D^2\varphi(x)[h,h]\bigr)^{1/2}.$$
--
--   This is the main result of the paper. It improves the bound $O(n)$ of Nesterov and Nemirovski to exactly $n$, which is optimal: no barrier for, e.g., the simplex or the cube has a smaller parameter.
--
--   **Formalization Note.** The conclusion is the published predicate `EntropicBarrier.Universal.IsNuSelfConcordantBarrier K φ n`, which is Definitions 1–2 of this paper: the barrier limit at every frontier point within $\operatorname{int}(K)$; self-concordance through `ConvexOptimization.IsSelfConcordantOn` on $\operatorname{int}(K)$ (convex, $C^3$, inequality (1) along every line $t\mapsto\varphi(x+th)$); and (2) in one-sided form, which is equivalent to the paper's two-sided $|D\varphi(x)[h]|$ because the left side is linear in $h$ and the right side even. $\varphi$ is a total function on $\mathbb R^n$ with junk values off $\operatorname{int}(K)$, which the predicate never reads. $K$ is not assumed closed or bounded.
-- source:
--   Lee & Yue, Universal Barrier is n-Self-Concordant, arXiv:1809.03011v4, p. 5, Theorem 2; Definitions 1–3, p. 3

import Mathlib
import Definitions.Def_UniversalBarrier_NSC_Model
import Definitions.Def_EntropicBarrier_Universal_SelfConcordantBarrier

open scoped RealInnerProductSpace
open MeasureTheory

namespace UniversalBarrier.NSC

theorem theorem_2 {n : ℕ} (hn : 1 ≤ n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsProperConvexDomain K) :
    EntropicBarrier.Universal.IsNuSelfConcordantBarrier K (universalBarrier K) (n : ℝ) := by sorry

end UniversalBarrier.NSC
