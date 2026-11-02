-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P95_lemma8
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P95.lemma8
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:27:54.921617+00:00
-- url     : https://prove2.me/theorems/7032c984-7223-45b9-bbc1-676a2859d00e
-- title:
--   Lemma 8: general-state PPT preparation SDP
-- statement:
--   All logarithms have base two. A PPT operation is a completely positive, trace-preserving map $L$ such that $\Gamma_{\rm out}L\Gamma_{\rm in}$ is completely positive for arbitrary finite ancillary systems; $\Gamma$ transposes Bob in the fixed product basis. For a positive integer $K$, $\Phi_K$ denotes the maximally entangled state of Schmidt rank $K$. Let $\rho$ be any density operator on any nonempty finite-dimensional product space $\mathcal H_A\otimes\mathcal H_B$, allowing unequal local dimensions, mixed states, and zero eigenvalues. For $K\ge2$, the following minimum is attained:
--
--   $$v=\min\{\operatorname{Tr}P:P=P^\dagger\ge0,\;-(K-1)P^\Gamma\le\rho^\Gamma\le(K+1)P^\Gamma\}.$$
--
--   Then $\Phi_K\to^{\rm PPT}\rho$ if and only if $v\le1$. All matrix inequalities are Loewner inequalities and use the same $P$.
--
--   This is the general finite-dimensional preparation SDP.
-- source:
--   Pure-state transformations and catalysis under operations that completely preserve positivity of partial transpose, arXiv:0801.4322v2, PDF p. 5, Lemma 8: general-state PPT preparation SDP

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P95

noncomputable section

open scoped BigOperators Matrix ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P95

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact primitives from the pinned accepted library; no local aliases.

open QAlgorithms.Papers.Independent.Claimed50.P28 (maximallyEntangledDensity)

open QAlgorithms.Papers.Independent.Information100.P27 (IsProbability)

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

open QAlgorithms.Papers.Independent.Information100.P19 (outer)

open QAlgorithms.Papers.Independent.Dependency50.P18 (bipartiteTensor)

open QAlgorithms.Papers.Independent.Support50.P11 (Loewner)

/-- PDF p.5, Lemma 8: arbitrary mixed or pure state, arbitrary rectangular local dimensions.
IsLeast preserves the source's minimum and rules out default real infima. -/
theorem lemma8 {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (K : ℕ) (hK : 2 ≤ K) (X : Matrix (A × B) (A × B) ℂ)
    (hstate : QAlgorithms.IsDensityMatrix X) :
    IsLeast (preparationValues K X) (preparationValue K X) ∧
      (Reach (maximallyEntangledDensity K) X ↔ preparationValue K X ≤ 1) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P95

end
