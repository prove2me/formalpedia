-- Prove2me | Theorems.Thm_SimchiLeviAddOn_Learning_lemma_3
-- name    : SimchiLeviAddOn.Learning.lemma_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T01:59:06.923656+00:00
-- url     : https://prove2.me/theorems/82dc8654-4e73-4b7b-8a33-5565fb132b3f
-- title:
--   Lemma 3 — Algorithm 1 approximation error
-- statement:
--   For every operational instance, every demand table in [0,1], every integer K >= 1, and every output p recovered by Algorithm 1, including all ties,
--
--   $$R^*-R(p) \le \widehat p MN/K.$$
--
--   The benchmark maximizes over exactly the policies feasible for (1). R(p) is actual expected revenue. Output feasibility is not assumed and approximate DP revenue is not substituted for actual revenue.
--
--   Differences from the source:
--   - encoding: positive product counts and finite nonempty nonnegative real price sets → positive natural dimensions and injectively labelled real menus with Fin indices; reason: every finite real menu admits this labelling; cardinalities, arbitrary real values and ties are preserved
--   - reading: the supportive index set is printed as {1,...,N} on page 7 → supportive products use Fin M; reason: all revenue formulas and algorithms consistently use M supportive products
--   - encoding: a maximum over the stated feasible set → the real supremum of that finite nonempty feasible revenue set; reason: the maximum is attained; nonemptiness excludes only an undefined source optimum
--   - encoding: nearest rounding, sorting and recovery along maximizing DP transitions → all nearest grid integers, maximizing price witnesses, descending permutations and maximizing transitions from zero; reason: all ties are retained; the recursion visits only reachable grid sums
--   - encoding: an unselected supportive product does not use a discount price → its unused discount label may be any menu member; reason: the label affects neither revenue nor feedback; no feasibility of an algorithm output is assumed
-- source:
--   Simchi-Levi, Sun and Zhang, arXiv:2005.00947v1 (2 May 2020), https://arxiv.org/abs/2005.00947v1, Lemma 3, p. 13 (same PDF page)

import Definitions.Def_SimchiLeviAddOn_Learning_Offline

namespace SimchiLeviAddOn.Learning

theorem lemma_3 (X : Market) (d : Tables X) (hd : IsDemand X d)
    (hX : Operational X) (K : ℕ) (hK : 1 ≤ K) (p : Policy X)
    (hp : IsOfflineOutput X d K p) :
    optimum X d - revenue X d p ≤ priceScale X * X.M * X.N / K := by sorry

end SimchiLeviAddOn.Learning
