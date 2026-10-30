-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P18_weighted_transposition_restriction
-- name    : QAlgorithms.Papers.Independent.Extend50.P18.weighted_transposition_restriction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:58:21.847996+00:00
-- url     : https://prove2.me/theorems/c74470c1-524c-4018-bdad-938b5db943a2
-- title:
--   Lemma 3: weighted transposition sum on a restriction block
-- statement:
--   Let $d\ge1$, $n\ge1$, $\mu\vdash_d n$, and let $\beta\vdash_d n-1$ be a one-box restriction of $\mu$. Let $P^\mu_\beta$ project onto that constituent inside the actual Specht module for $\mu$. Define $\widetilde\phi^\mu(a,n)=\phi^\mu((a,n))$ for $a<n$ and $\widetilde\phi^\mu(n,n)=dI$. With physical Schur multiplicities $m_\mu,m_\beta$ and irrep dimensions $d_\mu,d_\beta$,
--
--   $$
--   P^\mu_\beta\left(\sum_{a=1}^n\widetilde\phi^\mu(a,n)\right)P^\mu_\beta
--   =\frac{n m_\mu d_\beta}{m_\beta d_\mu}P^\mu_\beta.
--   $$
--
--   This identifies the scalar of the weighted transposition sum on each restriction block. The projector is constructed by the subgroup character sum.
--
--   **Formalization Note** The code writes $n=t+1$.
-- source:
--   Efficient multi port-based teleportation schemes, arXiv:2008.00984v4, PDF p. 10, Lemma 3

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P18

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P18

attribute [local instance] Classical.propDecidable

/-- Lemma 3: on any occurring one-box beta constituent, the weighted sum is
n*m_mu*d_beta/(m_beta*d_mu) times identity (PDF p.10, (46),(56)). The block
identity is expressed by multiplying the independently defined projector. -/
theorem weighted_transposition_restriction (d t : ℕ) (hd : 0 < d)
    (mu : QAlgorithms.Schur.Partition d (t+1)) (beta : QAlgorithms.Schur.Partition d t)
    (hbranch : beta.val ≤ mu.val) :
    restrictionProjector mu beta * weightedTranspositions mu * restrictionProjector mu beta =
      (((t+1 : ℕ) : ℂ) * (mpbtSchurMultiplicity mu : ℂ) * (irrepDim beta : ℂ) /
        ((mpbtSchurMultiplicity beta : ℂ) * (irrepDim mu : ℂ))) • restrictionProjector mu beta := by sorry

end QAlgorithms.Papers.Independent.Extend50.P18

end
