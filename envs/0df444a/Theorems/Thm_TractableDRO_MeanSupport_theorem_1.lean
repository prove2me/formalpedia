-- Prove2me | Theorems.Thm_TractableDRO_MeanSupport_theorem_1
-- name    : TractableDRO.MeanSupport.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:16:36.827157+00:00
-- url     : https://prove2.me/theorems/dc6d66b5-115b-4aff-9c29-d36f5260095a
-- title:
--   Theorem 1, p. 909 — π¹(r⁰, r) of (21) is a tight upper bound: sup over 𝔽₁ of E_ℙ((r⁰ + r′ζ̃)⁺) = π¹(r⁰, r)
-- statement:
--   This is Theorem 1 of Goh and Sim (2010), the mean-and-support bound on the expected positive part of an affine function of a random vector.
--
--   Let $\mathcal V, \widehat{\mathcal V} \subseteq \mathbb R^n$ be closed convex sets such that $\widehat{\mathcal V}$ meets the interior of $\mathcal V$. Let $\mathbb F_1$ be the family of all probability distributions $\mathbb P$ of a random vector $\tilde\zeta \in \mathbb R^n$ such that $\tilde\zeta$ has support in $\mathcal V$ and its mean has support in $\widehat{\mathcal V}$:
--   $$\mathbb F_1 = \{\mathbb P : \hat\zeta = \mathbb E_{\mathbb P}(\tilde\zeta) \in \widehat{\mathcal V},\ \mathbb P(\tilde\zeta \in \mathcal V) = 1\}.$$
--   Then for every $r^0 \in \mathbb R$ and $r \in \mathbb R^n$,
--   $$\sup_{\mathbb P \in \mathbb F_1} \mathbb E_{\mathbb P}\big((r^0 + r'\tilde\zeta)^+\big) = \pi^1(r^0, r) = \inf_{s \in \mathbb R^{n}} \Big( \sup_{\hat\zeta \in \widehat{\mathcal V}} \{s'\hat\zeta\} + \sup_{\zeta \in \mathcal V} \max\{r^0 + r'\zeta - s'\zeta,\ -s'\zeta\} \Big),$$
--   with both sides in the extended reals $[-\infty, +\infty]$.
--
--   The theorem replaces an optimization over an infinite-dimensional family of distributions by a finite-dimensional convex program over the given sets. In the paper it bounds the expected positive part of a segregated linear decision rule and feeds the deflected linear decision rules of §6.
--
--   **Formalization Note** Distributions are probability measures on `Fin n → ℝ` with integrable coordinates; the mean is `MomentDRO.Conf.meanVec`; $\mathbb P(\tilde\zeta\in\mathcal V)=1$ is an almost-everywhere statement. Both sides are `EReal`, with the paper's convention that an infeasible maximization (minimization) has value $-\infty$ ($+\infty$); the paper's "inf" in (21) is `⨅`. The sets are closed and convex (the paper's tractable conic representable sets). The constraint qualification $\widehat{\mathcal V} \cap \operatorname{int}\mathcal V \ne \emptyset$ is added: as printed the theorem is false when $\mathbb F_1 = \emptyset$ (for $\mathcal V = \{(a,b) : a > 0,\ b \ge 1/a\}$, $\widehat{\mathcal V} = \{(a, 0) : a \in \mathbb R\}$ the left side is $-\infty$ and $\pi^1 \ge 0$), and the condition matches the paper's full-dimensionality assumptions (pp. 905–906). Under it both suprema in (21) are over nonempty sets, so the `EReal` sum $\bot + \top$ never arises.
-- source:
--   Goh & Sim, Distributionally Robust Optimization and Its Tractable Approximations, Oper. Res. 58(4), 2010, p. 909, Theorem 1, (21)

import Mathlib
import Definitions.Def_TractableDRO_MeanSupport_Model

open MeasureTheory

namespace TractableDRO.MeanSupport

theorem theorem_1 {n : ℕ} (V Vhat : Set (Fin n → ℝ))
    (hVconv : Convex ℝ V) (hVclosed : IsClosed V)
    (hVhconv : Convex ℝ Vhat) (hVhclosed : IsClosed Vhat)
    (hCQ : (Vhat ∩ interior V).Nonempty) (r0 : ℝ) (r : Fin n → ℝ) :
    worstCase (family1 V Vhat) r0 r = pi1 V Vhat r0 r := by sorry

end TractableDRO.MeanSupport
