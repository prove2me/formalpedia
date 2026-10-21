-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P06_longestIntertwiner
-- name    : QAlgorithms.Papers.Independent.Support21.P06.longestIntertwiner
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:38:07.932996+00:00
-- url     : https://prove2.me/theorems/295cdc2f-f624-49c7-b3d3-c547765ac614
-- title:
--   Longest evaluated intertwiner at a geometric-progression weight
-- statement:
--   Let $n\ge1$, let $q\in\mathbb C^\times$ be not a root of unity, and let $a\in\mathbb C^\times$. The finite Hecke algebra $H_n(q)$ has generators $T_1,\ldots,T_{n-1}$ satisfying $T_i^2=(q-q^{-1})T_i+1$ and the braid relations. Write $w_0(j)=n+1-j$ for the longest permutation in $S_n$ and $\ell(w)$ for the number of inversions of $w$.
--
--   Set $t=(a,aq^2,\ldots,aq^{2(n-1)})$. For any reduced expression $w_0=s_{i_1}\cdots s_{i_p}$, put $t^{(r)}=s_{i_{r+1}}\cdots s_{i_p}t$, where $(wt)_j=t_{w^{-1}(j)}$. Define the evaluated intertwiner by the ordered product
--   $$
--   \left.\tau_{w_0}\right|_t=\prod_{r=1}^p\left(T_{i_r}-\frac{(q-q^{-1})t^{(r)}_{i_r+1}}{t^{(r)}_{i_r+1}-t^{(r)}_{i_r}}\right),
--   $$
--   with increasing $r$ from left to right. Every denominator is nonzero, and
--   $$
--   \left.\tau_{w_0}\right|_t=\sum_{w\in S_n}(-q)^{\binom n2-\ell(w)}T_w,
--   $$
--   where $T_w$ is the generator product along any reduced expression of $w$.
--
--   This identity expresses the longest intertwiner as a normalized Hecke antisymmetrizer.
--
--   **Formalization Note** The equality is in the quotient of the free complex algebra by the finite Hecke relations. It is quantified over every auxiliary choice of reduced expressions; neither reduced-word independence nor the displayed identity is assumed as data.
-- source:
--   Skew shape representations are irreducible, arXiv:math/0401326v2, PDF p. 10, Proposition 3.6

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P06

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P06

open scoped BigOperators

open QAlgorithms.Papers.Independent.Renew46.P26 (Adjacent nextPosition)

attribute [local instance] Classical.propDecidable

/-- Proposition 3.6, PDF p.10. The expression is an equality in the actual
finite Hecke quotient. Reduced expressions are arbitrary; no normalizing
factor is inserted. The natural subtraction is bounded since the longest
permutation has maximal length. The q=1 historical attribution is not used. -/
theorem longestIntertwiner
    (n : ℕ) (hn : 0 < n) (q : ℂ) (hq : GenericParameter q)
    (a : ℂ) (ha : a ≠ 0) (r : ReducedExpressions n) :
    WordDefined (r (Fin.revPerm : Equiv.Perm (Fin n))).val (progressionWeight q a) ∧
    tauEvaluatedWord q (r (Fin.revPerm : Equiv.Perm (Fin n))).val
      (progressionWeight q a) =
      ∑ w : Equiv.Perm (Fin n),
        ((-q) ^ (n.choose 2 - permLength w)) • heckeWord q (r w).val := by sorry

end QAlgorithms.Papers.Independent.Support21.P06

end
