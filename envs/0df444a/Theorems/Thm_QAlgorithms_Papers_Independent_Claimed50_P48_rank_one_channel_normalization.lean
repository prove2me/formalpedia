-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P48_rank_one_channel_normalization
-- name    : QAlgorithms.Papers.Independent.Claimed50.P48.rank_one_channel_normalization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:42:48.393867+00:00
-- url     : https://prove2.me/theorems/f4e72d0d-685c-4f43-b0a6-e7c25f762be6
-- title:
--   Rank-one Kraus map is a channel iff the frame sum is identity
-- statement:
--   Let arbitrary finite input vectors $\psi_\alpha$ and output vectors $\varphi_\alpha$ define the CP map $\Phi(X)=\sum_\alpha|\varphi_\alpha\rangle\langle\psi_\alpha|X|\psi_\alpha\rangle\langle\varphi_\alpha|$ on a nonzero finite input space. Then
--
--   $$\Phi\text{ is trace preserving}\quad\Longleftrightarrow\quad
--   \sum_\alpha\|\varphi_\alpha\|^2|\psi_\alpha\rangle\langle\psi_\alpha|=I.$$
--
--   Individual vectors need not be unit or orthogonal. The norm factors are the source's full frame normalization.
-- source:
--   On complementary channels and the additivity problem, arXiv:quant-ph/0509101v3, PDF p. 4, Rank-one Kraus map is a channel iff the frame sum is identity

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P48

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel environmentSwap)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble convexRoof)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D A2 B2 C2 K : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype A2] [DecidableEq A2] [Fintype B2] [DecidableEq B2]

variable [Fintype C2] [DecidableEq C2] [Fintype K] [DecidableEq K]

/-- PDF p.4, following (13): retain the weights ||phi_alpha||^2. -/
theorem rank_one_channel_normalization [Nonempty A]
    (psi : K → EuclideanSpace ℂ A) (phi : K → EuclideanSpace ℂ B) :
    IsChannel (krausApply (rankOneKraus psi phi)) ↔
      ∑ k, ((‖phi k‖ ^ 2 : ℝ) : ℂ) • pureDensity (psi k) = 1 := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P48

end
