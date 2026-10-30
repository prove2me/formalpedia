-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P07_productComparison_minima
-- name    : QAlgorithms.Papers.Independent.Advance50.P07.productComparison_minima
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:35:39.383834+00:00
-- url     : https://prove2.me/theorems/f3f964f9-c307-4638-8bc3-ada69ec227be
-- title:
--   Marginals attain the product-comparison entropy minima
-- statement:
--   Let $\rho^{AB}$ be a density operator on nonzero finite-dimensional registers, with marginals $\rho^A,\rho^B$. Let $\sigma^A\ge0$ satisfy $\operatorname{supp}\rho^A\subseteq\operatorname{supp}\sigma^A$. For the unnormalized-comparison quantum relative entropy $D(\rho\Vert\sigma)=\operatorname{Tr}\rho(\log_2\rho-\log_2\sigma)$, extended by $+\infty$ on support failure,
--
--   $$\min_{\xi^B\in\mathcal S(B)}D(\rho^{AB}\Vert\sigma^A\otimes\xi^B)=D(\rho^{AB}\Vert\sigma^A\otimes\rho^B),$$
--   $$\min_{\xi^B\in\mathcal S(B)}D(\rho^{AB}\Vert1_A\otimes\xi^B)=D(\rho^{AB}\Vert1_A\otimes\rho^B),$$
--   $$\min_{\omega^A\in\mathcal S(A),\xi^B\in\mathcal S(B)}D(\rho^{AB}\Vert\omega^A\otimes\xi^B)=D(\rho^{AB}\Vert\rho^A\otimes\rho^B).$$
--
--   The marginals are normalized and attain each minimum. These identities identify the comparison states in conditional entropy.
--
--   **Source correction.** The printed variable comparison domains merely require positivity. Trace-one constraints are restored from the proof's use of relative-entropy nonnegativity and the downstream definition (23); the fixed $\sigma^A$ is not normalized.
-- source:
--   The quantum capacity of channels with arbitrarily correlated noise, arXiv:0902.0158v5, PDF p. 5, Lemma 6, minimizers of relative entropy over a product comparison

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P07

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology

open Filter

namespace QAlgorithms.Papers.Independent.Advance50.P07

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P09 (relativeD petzD)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative Density elog)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P19 (marginalRA marginalRB)

open QAlgorithms.Papers.Independent.Support50.P21 (PositiveTensorBasis)

/-- Lemma 6, PDF p.5, (21). SOURCE CORRECTION: printed variable
comparisons xi>=0 and omega>=0 are constrained to trace one, required by
the proof's relative-entropy nonnegativity. The fixed sigma_A remains arbitrary
PSD with containing support. Each claimed minimum has its marginal witness. -/
theorem productComparison_minima {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Mat (A × B)) (hrho : IsDensityMatrix rho) (sigma : Mat A)
    (hsigma : sigma.PosSemidef) (hsupp : SupportIncluded (traceRight rho) sigma) :
    IsDensityMatrix (traceRight rho) ∧ IsDensityMatrix (traceLeft rho) ∧
    (∀ xi : {tau : Mat B // Density tau}, relativeD rho (Matrix.kronecker sigma (traceLeft rho)) ≤
      relativeD rho (Matrix.kronecker sigma xi.1)) ∧
    (∀ xi : {tau : Mat B // Density tau}, relativeD rho (Matrix.kronecker (1 : Mat A) (traceLeft rho)) ≤
      relativeD rho (Matrix.kronecker (1 : Mat A) xi.1)) ∧
    (∀ (omega : {tau : Mat A // Density tau}) (xi : {tau : Mat B // Density tau}),
      relativeD rho (Matrix.kronecker (traceRight rho) (traceLeft rho)) ≤
        relativeD rho (Matrix.kronecker omega.1 xi.1)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P07

end
