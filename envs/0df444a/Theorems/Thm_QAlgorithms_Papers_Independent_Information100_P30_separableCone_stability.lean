-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P30_separableCone_stability
-- name    : QAlgorithms.Papers.Independent.Information100.P30.separableCone_stability
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:19:56.009992+00:00
-- url     : https://prove2.me/theorems/19912719-1710-4dfd-b6a5-47eeaf96af1b
-- title:
--   Separable-cone stability
-- statement:
--   Let $A,B,A',B'$ be nonzero finite-dimensional complex spaces, and let $F_A:\mathcal B(A)\to\mathcal B(A')$ and $F_B:\mathcal B(B)\to\mathcal B(B')$ be complex-linear positive maps. Write $\mathrm{Sep}_+$ for the cone of finite sums of positive product operators. Then
--
--   $$(F_A\otimes F_B)[\mathrm{Sep}_+(A:B)]\subseteq\mathrm{Sep}_+(A':B').$$
--
--   Neither complete positivity nor trace preservation is required of these maps. Thus the closure also applies whenever the intermediate operator after local CP prefiltering and an intervening map is separable; it does not assert separability merely from prefiltering a positive input.
-- source:
--   Feasibility Ordering of Entanglement-Source Placement for Qubit Channels, arXiv:2609.18803v1, PDF p. 2, Lemma 1

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P30

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Information100.P30

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Lemma 1 (PDF p.2, Eq.(11)): positive local linear maps preserve the full
unnormalized separable cone, with arbitrary nonzero finite local input and output dimensions.
This also applies to an intermediate separable operator obtained after CP prefiltering. -/
theorem separableCone_stability {I J K L : Type*}
    [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    [Nonempty I] [Nonempty J] [Nonempty K] [Nonempty L]
    [DecidableEq I] [DecidableEq J]
    (F : MatrixMap I K) (G : MatrixMap J L)
    (hF : IsPositiveMap F) (hG : IsPositiveMap G) :
    ∀ X : Matrix (I × J) (I × J) ℂ, Entanglement.IsSeparablePositive X →
      Entanglement.IsSeparablePositive (tensorMap F G X) := by sorry

end QAlgorithms.Papers.Independent.Information100.P30

end
