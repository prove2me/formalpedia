-- Prove2me | Theorems.Thm_TractableDRO_MeanSupport_theorem_1_upper
-- name    : TractableDRO.MeanSupport.theorem_1_upper
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T01:16:29.9377+00:00
-- url     : https://prove2.me/theorems/ac80ae28-b30d-4171-a682-c74e66013c0f
-- title:
--   Theorem 1, p. 909 (upper-bound part) — sup over 𝔽₁ of E_ℙ((r⁰ + r′ζ̃)⁺) ≤ π¹(r⁰, r)
-- statement:
--   This is the upper-bound half of Theorem 1 of Goh and Sim (2010).
--
--   Let $\mathcal V, \widehat{\mathcal V} \subseteq \mathbb R^n$ be arbitrary sets, and let $\mathbb F_1$ be the family of probability distributions of a random vector $\tilde\zeta \in \mathbb R^n$ with integrable coordinates, mean $\mathbb E_{\mathbb P}(\tilde\zeta) \in \widehat{\mathcal V}$ and $\mathbb P(\tilde\zeta \in \mathcal V) = 1$. For every $r^0 \in \mathbb R$ and $r \in \mathbb R^n$,
--   $$\sup_{\mathbb P \in \mathbb F_1} \mathbb E_{\mathbb P}\big((r^0 + r'\tilde\zeta)^+\big) \le \pi^1(r^0, r) = \inf_{s \in \mathbb R^{n}} \Big( \sup_{\hat\zeta \in \widehat{\mathcal V}} \{s'\hat\zeta\} + \sup_{\zeta \in \mathcal V} \max\{r^0 + r'\zeta - s'\zeta,\ -s'\zeta\} \Big),$$
--   both sides taken in the extended reals.
--
--   The bound $\pi^1$ is a deterministic convex program over the sets $\mathcal V$ and $\widehat{\mathcal V}$, so this inequality turns an optimization over distributions into a tractable robust optimization problem.
--
--   **Formalization Note** No convexity, closedness or nonemptiness is assumed: the inequality holds for all sets. When $\mathbb F_1$ is empty the left side is $-\infty$ (`⊥`). All values are in `EReal`; see the definition `TractableDRO.MeanSupport.Model`.
-- source:
--   Goh & Sim, Distributionally Robust Optimization and Its Tractable Approximations, Oper. Res. 58(4), 2010, p. 909, Theorem 1 (upper-bound part), (21)

import Mathlib
import Definitions.Def_TractableDRO_MeanSupport_Model

open MeasureTheory

namespace TractableDRO.MeanSupport

theorem theorem_1_upper {n : ℕ} (V Vhat : Set (Fin n → ℝ)) (r0 : ℝ) (r : Fin n → ℝ) :
    worstCase (family1 V Vhat) r0 r ≤ pi1 V Vhat r0 r := by sorry

end TractableDRO.MeanSupport
