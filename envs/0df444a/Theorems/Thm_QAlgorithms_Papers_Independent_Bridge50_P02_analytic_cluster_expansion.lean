-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P02_analytic_cluster_expansion
-- name    : QAlgorithms.Papers.Independent.Bridge50.P02.analytic_cluster_expansion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:46:41.800133+00:00
-- url     : https://prove2.me/theorems/d490d30a-3f10-4318-9db1-ee893badd691
-- title:
--   Proposition 3: analytic bounded cluster expansion
-- statement:
--   On $\mathbb Z^d$, $d\ge1$, fix a nonzero finite-dimensional one-site space and two translation-invariant self-adjoint interactions $\Phi,\Psi$, with zero empty-support terms. Let $\beta_1,\beta_2,a,\delta>0$, and let $\mathcal X_0$ denote the finite supports containing the origin. Suppose
--   $$\sum_{X\in\mathcal X_0}e^{2a|X|}\left(e^{\delta(\beta_1\|\Phi_X\|+\beta_2\|\Psi_X\|)}-1\right)\le a.$$
--   For finite $X$, put $Z_X(z_1,z_2)=q^{-|X|}\operatorname{Tr}(e^{z_1\beta_1H_X^\Phi}e^{z_2\beta_2H_X^\Psi})$, where $q$ is the site dimension. Define the canonical cluster germs by subset Mobius inversion of the log germs of $Z_X$ at $(0,0)$, normalized by $\log Z_X(0,0)=0$. Every germ has an analytic continuation $w(C)$ to $\mathcal D=\{|z_1|<\delta,|z_2|<\delta\}$ and
--   $$\sup_{z\in\mathcal D}\sum_{C\in\mathcal X_0}|w_z(C)|\le a.$$
--
--   Both sums use their nonnegative extended meaning, so the bounds imply summability. The conclusion constructs continuations of these specific germs; the coefficients are not arbitrary unknown functions assumed to obey the bound.
-- source:
--   Second-order asymptotics for quantum hypothesis testing in settings beyond i.i.d. - quantum lattice systems and more, arXiv:1510.04682v4, PDF p. 19, Proposition 3

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P02

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Bridge50.P02

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P15
  (evaluate positiveMatrixRpow modularMatrix modularQuadratic resolventOverlap petzOverlap
    finiteRelativeEntropyNats)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower testingBeta)

open QAlgorithms.Papers.Independent.Information100.P58 (normalQuantile)

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Proposition 3, PDF p.19, (4.11)--(4.12): canonical germs have bounded analytic
continuations to the whole polydisc. The minus one is INSIDE the exponential prefactor.
No finite-range hypothesis is added to this summability theorem. -/
theorem analytic_cluster_expansion (d q : ℕ) (hd : 1 ≤ d) (hq : 0 < q)
    (Phi Psi : SpinInteraction d q)
    (hPhiTranslation : TranslationInvariant Phi) (hPsiTranslation : TranslationInvariant Psi)
    (beta1 beta2 a delta : ℝ) (hbeta1 : 0 < beta1) (hbeta2 : 0 < beta2)
    (ha : 0 < a) (hdelta : 0 < delta)
    (hsmall : ClusterSmallness Phi Psi beta1 beta2 a delta) :
    ∃ W : Finset (Site d) → (ℂ × ℂ) → ℂ,
      (∀ X, AnalyticOnNhd ℂ (W X) {z | ‖z.1‖ < delta ∧ ‖z.2‖ < delta}) ∧
      (∀ X, W X =ᶠ[nhds (0 : ℂ × ℂ)] clusterGerm Phi Psi beta1 beta2 X) ∧
      (∀ z : ℂ × ℂ, ‖z.1‖ < delta → ‖z.2‖ < delta →
        (∑' X : {X : Finset (Site d) // (0 : Site d) ∈ X},
          ENNReal.ofReal ‖W X.val z‖) ≤ ENNReal.ofReal a) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P02

end
