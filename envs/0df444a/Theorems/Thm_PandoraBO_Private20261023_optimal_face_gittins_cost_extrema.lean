-- Prove2me | Theorems.Thm_PandoraBO_Private20261023_optimal_face_gittins_cost_extrema
-- name    : PandoraBO.Private20261023.optimal_face_gittins_cost_extrema
-- status  : Proved
-- author  : @QianJaneXie
-- created : 2026-10-24T00:18:13.9583+00:00
-- url     : https://prove2.me/theorems/d0e2364b-53a6-4a6b-9a0c-b008a84283d3
-- title:
--   Lemma 8 bridge — Gittins tie rules realize optimal cost extremes
-- statement:
--   Fix $\lambda>0$. There exist two Gittins policies $\pi_-$ and $\pi_+$ whose expected costs bound the costs of every penalized-optimal policy:
--
--   $$C(\pi_-)\le C(\rho)\le C(\pi_+)\qquad(\rho\text{ optimal at }\lambda).$$
--
--   For every $a\in[0,1]$, there also exists a Gittins policy with expected cost
--
--   $$aC(\pi_-)+(1-a)C(\pi_+).$$
--
--   By Theorem 1, the two witnesses and the interpolating policies are themselves penalized-optimal. This is an additional bridge required by the budget argument; it is not claimed to be a verbatim numbered lemma in the paper. It makes explicit both extreme-cost attainment within the Gittins class and randomization through admissible ties.
-- source:
--   Qian Xie, Raul Astudillo, Peter I. Frazier, Ziv Scully, and Alexander Terenin. [Cost-aware Bayesian Optimization via the Pandora's Box Gittins Index](https://arxiv.org/abs/2406.20062). NeurIPS 2024. Appendix B.5, Lemma 8 and the conclusion of Theorem 2. This is a supporting formalization lemma for expected-cost extrema among optimal Gittins policies, not a separately numbered theorem in the paper.

import Definitions.Def_PandoraBO_Model

set_option autoImplicit false

namespace PandoraBO.Private20261023

theorem optimal_face_gittins_cost_extrema {n : ℕ} (M : Instance n)
    (multiplier : ℝ) (hpos : 0 < multiplier) :
    ∃ low high : Policy n,
      isGittinsPolicy M multiplier low ∧ isGittinsPolicy M multiplier high ∧
      (∀ π : Policy n, optimal M multiplier π →
        expectedCost M low ≤ expectedCost M π ∧ expectedCost M π ≤ expectedCost M high) ∧
      ∀ a : ℝ, 0 ≤ a → a ≤ 1 → ∃ π : Policy n,
        isGittinsPolicy M multiplier π ∧
        expectedCost M π = a * expectedCost M low + (1 - a) * expectedCost M high := by sorry

end PandoraBO.Private20261023
