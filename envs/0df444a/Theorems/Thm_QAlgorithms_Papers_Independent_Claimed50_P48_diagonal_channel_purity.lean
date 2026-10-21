-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P48_diagonal_channel_purity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P48.diagonal_channel_purity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:48:44.782756+00:00
-- url     : https://prove2.me/theorems/005d289f-47b5-4573-b223-9ae45772d82e
-- title:
--   Diagonal channels have a pure fixed basis and extremal purity
-- statement:
--   Let $c$ be a positive semidefinite matrix on a nonzero finite coordinate space with $c_{aa}=1$ for every $a$. The Schur map $\Phi(X)=c\circ X$ is a channel and fixes every canonical basis density:
--
--   $$\Phi(|e_a\rangle\langle e_a|)=|e_a\rangle\langle e_a|,\qquad
--   \nu_p(\Phi)=1\ (1\le p\le\infty),\qquad\check H(\Phi)=0.$$
--
--   The scalar claims use channel normalization. The fixed pure basis provides the extremal inputs discussed on pages 5–6.
-- source:
--   On complementary channels and the additivity problem, arXiv:quant-ph/0509101v3, PDF p. 5, Diagonal channels have a pure fixed basis and extremal purity

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

/-- PDF pp.5–6: canonical basis densities are fixed. Scalar extrema require
trace preservation and include the infinity endpoint. -/
theorem diagonal_channel_purity [Nonempty A] (c : Matrix A A ℂ)
    (hc : c.PosSemidef) (hdiag : ∀ a, c a a = 1) :
    IsChannel (Matrix.hadamard c) ∧ (∀ a : A, Matrix.hadamard c (pureDensity (ket a)) = pureDensity (ket a)) ∧
    (∀ p : ℝ≥0∞, ValidExponent p → nu p (Matrix.hadamard c) = 1) ∧ hmin (Matrix.hadamard c) = 0 := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P48

end
