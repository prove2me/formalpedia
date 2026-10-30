-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P14_stability
-- name    : QAlgorithms.Papers.Independent.Advance50.P14.stability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:22:39.769921+00:00
-- url     : https://prove2.me/theorems/92bb3849-7708-4a3d-b860-67013edfcc0a
-- title:
--   Lemma VI.1, equation (23): stability
-- statement:
--   All systems are finite-dimensional complex multipartite systems with at least two parties and positive local dimensions. Every state is positive semidefinite with trace one. Separability means a convex mixture of products across all parties. Logarithms are base two, and the trace norm has no factor of one half. Fix states $\rho,\sigma,\pi_1,\pi_2$, including the finite dimensions of both auxiliaries. Suppose there is a sequence $\epsilon_j\ge0$ tending to zero such that the following weighted-copy conversion holds for every $j$:
--
--   $$\rho\otimes\pi_1^{\otimes\epsilon_j}\prec\sigma\otimes\pi_2^{\otimes\epsilon_j}.\quad\text{Then}\quad\rho\prec\sigma.$$
--
--   The auxiliary states are fixed before the vanishing sequence and all block protocols. Real exponents specify integer-copy limiting rates, with zero weight realized by zero copies. This is stability of the asymptotic order.
-- source:
--   A reversible theory of entanglement and its relation to the second law, arXiv:0710.5827v3, PDF p. 18, Lemma VI.1, equation (23): stability

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P14

noncomputable section

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis)

open scoped Matrix ComplexOrder ENNReal NNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Advance50.P14

/-- PDF p.18, Lemma VI.1, Eq.(23): stability with two FIXED auxiliary
states and a nonnegative sequence of copy weights tending to zero.
Formula pi1,pi2 is followed; the prose's pi0,pi1 is a label typo.
The hypothesis is existence of one vanishing sequence, not all epsilon>0. -/
theorem stability {m : ℕ} (X Y P Q : PhysicalState m)
    (h : ∃ epsilon : ℕ → ℝ≥0,
      Tendsto (fun j => (epsilon j : ℝ)) atTop (nhds 0) ∧
      ∀ j, WeightedConverts (pairFamily X P 1 (epsilon j))
        (pairFamily Y Q 1 (epsilon j))) :
    AsymptoticConverts X.system X.density Y.system Y.density := by sorry

end QAlgorithms.Papers.Independent.Advance50.P14

end
