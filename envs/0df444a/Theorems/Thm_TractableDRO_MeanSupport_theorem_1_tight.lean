-- Prove2me | Theorems.Thm_TractableDRO_MeanSupport_theorem_1_tight
-- name    : TractableDRO.MeanSupport.theorem_1_tight
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:16:33.714322+00:00
-- url     : https://prove2.me/theorems/be7e4a84-4958-49e1-a994-963c66758cb5
-- title:
--   Theorem 1, p. 909 (tightness part) — π¹(r⁰, r) ≤ sup over 𝔽₁ of E_ℙ((r⁰ + r′ζ̃)⁺)
-- statement:
--   This is the tightness half of Theorem 1 of Goh and Sim (2010).
--
--   Let $\mathcal V, \widehat{\mathcal V} \subseteq \mathbb R^n$ be closed convex sets such that $\widehat{\mathcal V}$ meets the interior of $\mathcal V$, and let $\mathbb F_1$ be the family of probability distributions of $\tilde\zeta \in \mathbb R^n$ with integrable coordinates, mean $\mathbb E_{\mathbb P}(\tilde\zeta) \in \widehat{\mathcal V}$ and $\mathbb P(\tilde\zeta \in \mathcal V) = 1$. For every $r^0 \in \mathbb R$ and $r \in \mathbb R^n$,
--   $$\pi^1(r^0, r) = \inf_{s \in \mathbb R^{n}} \Big( \sup_{\hat\zeta \in \widehat{\mathcal V}} \{s'\hat\zeta\} + \sup_{\zeta \in \mathcal V} \max\{r^0 + r'\zeta - s'\zeta,\ -s'\zeta\} \Big) \le \sup_{\mathbb P \in \mathbb F_1} \mathbb E_{\mathbb P}\big((r^0 + r'\tilde\zeta)^+\big),$$
--   both sides taken in the extended reals.
--
--   Together with the upper-bound half, this says that $\pi^1$ cannot be improved using only the support and mean information.
--
--   **Formalization Note** The sets of the paper are tractable conic representable, which is modelled as closed and convex. The condition $\widehat{\mathcal V} \cap \operatorname{int}\mathcal V \ne \emptyset$ is not on the page. It is a constraint qualification: without it the statement is false (for $\mathcal V = \{(a,b) : a > 0,\ b \ge 1/a\}$ and $\widehat{\mathcal V} = \{(a, 0)\}$ the family is empty, the left side of Theorem 1 is $-\infty$ and $\pi^1 \ge 0$). It is in line with the paper's full-dimensionality assumptions (pp. 905–906), and it implies $\mathbb F_1 \ne \emptyset$.
-- source:
--   Goh & Sim, Distributionally Robust Optimization and Its Tractable Approximations, Oper. Res. 58(4), 2010, p. 909, Theorem 1 (tightness part), (21)

import Mathlib
import Definitions.Def_TractableDRO_MeanSupport_Model

open MeasureTheory

namespace TractableDRO.MeanSupport

theorem theorem_1_tight {n : ℕ} (V Vhat : Set (Fin n → ℝ))
    (hVconv : Convex ℝ V) (hVclosed : IsClosed V)
    (hVhconv : Convex ℝ Vhat) (hVhclosed : IsClosed Vhat)
    (hCQ : (Vhat ∩ interior V).Nonempty) (r0 : ℝ) (r : Fin n → ℝ) :
    pi1 V Vhat r0 r ≤ worstCase (family1 V Vhat) r0 r := by sorry

end TractableDRO.MeanSupport
