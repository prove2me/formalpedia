-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P21_covariantNormalization
-- name    : QAlgorithms.Papers.Independent.Claimed50.P21.covariantNormalization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:05:55.527585+00:00
-- url     : https://prove2.me/theorems/96fea3fa-1f5f-40e5-99ab-96bf273cf430
-- title:
--   Trace normalization of a covariant seed
-- statement:
--   Let $d\ge2$ and use normalized Haar measure on $\mathrm{SU}(d)$. Let $\Xi$ be a positive semidefinite operator on the four wires $(3,2,1,0)$, each identified with $\mathbb C^d$, and suppose $\Xi$ commutes with $V_3\otimes V_2^*\otimes V_1\otimes V_0^*$ for every $V\in\mathrm{SU}(d)$. Set $R_V=A(V,I_d)\Xi A(V,I_d)^\dagger$ using the covariance representation above. Then
--
--   $$
--   \int dV\,R_V\text{ is a deterministic two-comb}\quad\Longleftrightarrow\quad\operatorname{Tr}\Xi=d^2.
--   $$
--
--   Here deterministic means positivity together with $\operatorname{Tr}_3R=I_2\otimes R^{(1)}$ for some positive $R^{(1)}$, and $\operatorname{Tr}_1R^{(1)}=I_0$, in the unnormalized Choi convention.
--
--   The result reduces causal normalization to a trace constraint within this symmetry class.
-- source:
--   Information - Disturbance Tradeoff in the Estimation of a Unitary Transformation, arXiv:1006.5665v2, PDF p. 6, §IV B, Eq.(25)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P21

noncomputable section

open MeasureTheory

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P21

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P21.matrixMeasurable

/-- PDF p.6, Eq.(25): trace normalization is equivalent to deterministic-comb
normalization only under positivity and the diagonal seed commutant. -/
theorem covariantNormalization (d : ℕ) (hd : 2 ≤ d) (H : HaarLaw d)
    (X : Matrix (Four d) (Four d) ℂ) (hX : X.PosSemidef) (hc : SeedCommutes X) :
    IsDeterministicTwoComb (∫ V, covariantDensity X V ∂H.law) ↔ X.trace = (d : ℂ)^2 := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P21

end
