-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P26_hookBranching
-- name    : QAlgorithms.Papers.Independent.Next46.P26.hookBranching
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:05:30.171991+00:00
-- url     : https://prove2.me/theorems/ebf5ffa6-3bee-4d39-9ee8-cb962f91429e
-- title:
--   Hook-product branching in its equivalent forms
-- statement:
--   Let $\lambda$ be a nonempty Young diagram with $n$ cells. Let $h_z$ be the size of the hook at $z$, let $H_\lambda=\prod_{z\in[\lambda]}h_z$, and write $\mu\to\lambda$ when $\mu$ is a Young diagram obtained by removing one corner. Define $D_{rs}=\{(i,j)\in[\lambda]\setminus C[\lambda]:i\ne r,\ j\ne s\}$. Then the following hook-product branching formulas hold, with all quotients interpreted in $\mathbb Q$:
--   $$
--   \frac{n!}{H_\lambda}=\sum_{\mu\to\lambda}\frac{(n-1)!}{H_\mu},\qquad
--   \sum_{\mu\to\lambda}\frac{(n-1)!}{n!}\frac{H_\lambda}{H_\mu}=1,
--   $$
--   $$
--   \sum_{(r,s)\in C[\lambda]}\frac1n\prod_{i=1}^{r-1}\frac{h_{is}}{h_{is}-1}\prod_{j=1}^{s-1}\frac{h_{rj}}{h_{rj}-1}=1,
--   $$
--   $$
--   n\prod_{z\in[\lambda]\setminus C[\lambda]}(h_z-1)=\sum_{(r,s)\in C[\lambda]}\left(\prod_{i=1}^{r-1}h_{is}\right)\left(\prod_{j=1}^{s-1}h_{rj}\right)\prod_{z\in D_{rs}}(h_z-1).
--   $$
--   These are the rational, ratio and cleared-denominator versions of the hook branching rule used in the hook length formula.
-- source:
--   The weighted hook length formula, arXiv:1006.0043v1, PDF p. 1, BRHL; equations (1)–(3)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- BRHL and its equivalent forms (1), (2), (3), pp.1,3–4. The second
clause includes the hook-ratio rewriting of (2); all differences are in ℚ. -/
theorem hookBranching (lam : YoungDiagram) (hne : lam.cells.Nonempty) :
    ((lam.card.factorial : ℚ) / hookProduct lam =
      ∑ mu ∈ oneBoxPredecessors lam, ((lam.card - 1).factorial : ℚ) / hookProduct mu) ∧
    ((∑ mu ∈ oneBoxPredecessors lam,
      (((lam.card - 1).factorial : ℚ) / (lam.card.factorial : ℚ)) *
        (hookProduct lam / hookProduct mu)) = 1) ∧
    ((∑ z ∈ corners lam, (1 / (lam.card : ℚ)) *
      (∏ i ∈ Finset.range z.1,
        (hook lam (i, z.2) : ℚ) / ((hook lam (i, z.2) : ℚ) - 1)) *
      ∏ j ∈ Finset.range z.2,
        (hook lam (z.1, j) : ℚ) / ((hook lam (z.1, j) : ℚ) - 1)) = 1) ∧
    ((lam.card : ℚ) * (∏ z ∈ noncorners lam, ((hook lam z : ℚ) - 1)) =
      ∑ z ∈ corners lam,
        (∏ i ∈ Finset.range z.1, (hook lam (i, z.2) : ℚ)) *
        (∏ j ∈ Finset.range z.2, (hook lam (z.1, j) : ℚ)) *
        ∏ u ∈ offCross lam z.1 z.2, ((hook lam u : ℚ) - 1)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P26

end
