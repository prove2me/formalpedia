-- Prove2me | Theorems.Thm_UniversalBarrier_NSC_barrier_property
-- name    : UniversalBarrier.NSC.barrier_property
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:52.993484+00:00
-- url     : https://prove2.me/theorems/c08ab0eb-cb53-453a-b812-a68f3c460d53
-- title:
--   Proof of Theorem 2, p. 5 — the universal barrier φ is a barrier on K
-- statement:
--   Let $n\ge1$ and let $K\subseteq\mathbb R^n$ be a proper convex domain (convex, non-empty interior, containing no line). Let $\varphi(x)=\log\mathrm{Vol}_n(K^\circ(x))$ be its universal barrier, where $K^\circ(x)=\{y:\ y^{\mathsf T}(z-x)\le1\ \forall z\in K\}$. Then $\varphi$ is a barrier on $K$: for every boundary point $x_0$ of $K$,
--   $$\varphi(x)\to+\infty\qquad\text{as } x\to x_0,\ x\in\operatorname{int}(K).$$
--
--   This is the first part of Theorem 2; the paper cites it from Nesterov and Nemirovski [10, Theorem 2.5.1].
--
--   **Formalization Note.** "Barrier" is the published predicate `EntropicBarrier.Universal.IsBarrier` (Definition 1 of this paper): the limit is taken at every point of the frontier of $K$, within $\operatorname{int}(K)$. $K$ need not be closed or bounded.
-- source:
--   Lee & Yue, Universal Barrier is n-Self-Concordant, arXiv:1809.03011v4, p. 5, proof of Theorem 2 (citing [10, Theorem 2.5.1]); Definition 1, p. 3

import Mathlib
import Definitions.Def_UniversalBarrier_NSC_Model
import Definitions.Def_EntropicBarrier_Universal_SelfConcordantBarrier

open scoped RealInnerProductSpace
open MeasureTheory

namespace UniversalBarrier.NSC

theorem barrier_property {n : ℕ} (hn : 1 ≤ n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsProperConvexDomain K) :
    EntropicBarrier.Universal.IsBarrier K (universalBarrier K) := by sorry

end UniversalBarrier.NSC
