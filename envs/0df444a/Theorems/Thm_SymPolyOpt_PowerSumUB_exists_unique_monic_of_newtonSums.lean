-- Prove2me | Theorems.Thm_SymPolyOpt_PowerSumUB_exists_unique_monic_of_newtonSums
-- name    : SymPolyOpt.PowerSumUB.exists_unique_monic_of_newtonSums
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:23:02.795109+00:00
-- url     : https://prove2.me/theorems/e6a93790-9472-4abd-a88c-182162b64597
-- title:
--   §6.2, p. 27 — s_1, …, s_{m−1} determine p_{m−1}, …, p_1, so p_0 is the only unknown
-- statement:
--   Let $m \ge 1$, let $\gamma_1, \dots, \gamma_{m-1}$ be real numbers and let $p_0 \in \mathbb{R}$. Then there is exactly one monic real polynomial $p$ of degree $m$ with constant coefficient $p_0$ whose Newton sums satisfy
--   $$s_j(p) = \gamma_j, \qquad j = 1, \dots, m-1.$$
--
--   Uniqueness is the paper's remark that the Newton sums $s_1, \dots, s_{m-1}$ determine the coefficients $p_{m-1}, \dots, p_1$; existence is what allows the constant coefficient $p_0$ to range freely as the single unknown of the SDP (6.7). Together they identify the feasible set of (6.7) over $p_0$ with the set of monic degree-$m$ polynomials with the prescribed Newton sums.
-- source:
--   Riener, Theobald, Jansson Andrén and Lasserre, Exploiting symmetries in SDP-relaxations for polynomial optimization, arXiv:1103.0486v3, p. 27, §6.2, "If one knows s_j for all j = 1, ..., m − 1, then one may compute the p_j's ..."

import Mathlib
import Definitions.Def_SymPolyOpt_PowerSumUB_Setting

namespace SymPolyOpt.PowerSumUB

open Polynomial

theorem exists_unique_monic_of_newtonSums (m : ℕ) (hm : 1 ≤ m) (γ : ℕ → ℝ) (p₀ : ℝ) :
    ∃! p : ℝ[X], p.Monic ∧ p.natDegree = m ∧ p.coeff 0 = p₀ ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ m - 1 → newtonSum p j = γ j := by sorry

end SymPolyOpt.PowerSumUB
