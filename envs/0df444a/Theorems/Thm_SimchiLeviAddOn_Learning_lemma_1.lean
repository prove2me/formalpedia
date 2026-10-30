-- Prove2me | Theorems.Thm_SimchiLeviAddOn_Learning_lemma_1
-- name    : SimchiLeviAddOn.Learning.lemma_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T01:58:28.245237+00:00
-- url     : https://prove2.me/theorems/2d2f4752-787b-448b-9936-091eb5023740
-- title:
--   Lemma 1 — Lipschitz constant for the printed supportive subproblem
-- statement:
--   For arbitrary demand tables in [0,1] and nonempty feasible set of literal equation (3), let R_s(gamma) be its attained maximum. For every gamma, delta >= 0,
--
--   $$|R_s(\gamma)-R_s(\delta)| \le M\widehat p |\gamma-\delta|.$$
--
--   The price scale is the maximum over core and original prices. Equation (3) is used literally: original < discount. Feasibility of the distinct problem (1) is not assumed. The printed lemma is preserved, including its counterexample in I1.
--
--   Differences from the source:
--   - encoding: positive product counts and finite nonempty nonnegative real price sets → positive natural dimensions and injectively labelled real menus with Fin indices; reason: every finite real menu admits this labelling; cardinalities, arbitrary real values and ties are preserved
--   - reading: the supportive index set is printed as {1,...,N} on page 7 → supportive products use Fin M; reason: all revenue formulas and algorithms consistently use M supportive products
--   - encoding: a maximum over the stated feasible set → the real supremum of that finite nonempty feasible revenue set; reason: the maximum is attained; nonemptiness excludes only an undefined source optimum
-- source:
--   Simchi-Levi, Sun and Zhang, arXiv:2005.00947v1 (2 May 2020), https://arxiv.org/abs/2005.00947v1, Lemma 1, p. 10 (same PDF page)

import Definitions.Def_SimchiLeviAddOn_Learning_Model

namespace SimchiLeviAddOn.Learning

theorem lemma_1 (X : Market) (d : Tables X) (hd : IsDemand X d)
    (hX : ∃ p : Policy X, PrintedFeasible X p) :
    ∀ γ δ : ℝ, 0 ≤ γ → 0 ≤ δ →
      |printedSupportiveValue X d γ - printedSupportiveValue X d δ| ≤
        (X.M : ℝ) * priceScale X * |γ - δ| := by sorry

end SimchiLeviAddOn.Learning
