-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P53_eve_ensembles
-- name    : QAlgorithms.Papers.Independent.Intake100.P53.eve_ensembles
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:46:56.983084+00:00
-- url     : https://prove2.me/theorems/2a1d6c9f-9f14-4b4d-b1f0-21edfbead59c
-- title:
--   §§IV–V, (18)–(21): constructed conditional pure states and DR/RR ensembles
-- statement:
--   Let $\kappa>0$, $0<\eta\le1$, and $\delta\ge0$ be finite real parameters. Alice modulates normalized oscillator coherent states with density $\exp(-|\alpha|^2/(2\kappa))/(2\pi\kappa)$ relative to planar Lebesgue measure. Bob's tomographically verified output is $D(\sqrt\eta\alpha)\tau_{\delta/2}D(\sqrt\eta\alpha)^\dagger$, where $\tau_n$ is the thermal state of mean photon number $n$, and he uses ideal heterodyne detection. Bits are the signs of the real parts, with bit zero for a nonnegative real part. Public announcements are $a=(u,y)=(|\Re\alpha|,\Im\alpha)$ and $b=(w,z)=(|\Re\beta|,\Im\beta)$. Zero-real-part events have probability zero. All formulas below concern the source's collective-attack, infinite-key setting with completed tomography; they assert no finite-sample or coherent-attack security.
--
--   Fix one pure isometric collective interaction $V$ before choosing $\alpha$. Construct the coherent-bra branch from its full oscillator coefficients. Its coefficient sums converge, its squared norm is $\pi p(\beta\mid\alpha)>0$, and its normalized vector $\epsilon^{\alpha,\beta}$ has norm one. For fixed announcements let $D_{ij}$ be the projector on that vector at $\alpha_i=(-1)^i u+\mathrm{i}y$, $\beta_j=(-1)^j w+\mathrm{i}z$. Let $\epsilon^{a,b}$ and its Alice-bit and Bob-bit conditional states be computed using the actual density disintegration, rather than chosen freely. Then all these operators are normalized positive trace-class densities and
--
--   $$\epsilon^{a,b}=\tfrac12[(1-e)(D_{00}+D_{11})+e(D_{01}+D_{10})]=\tfrac12(\epsilon_0+\epsilon_1)=\tfrac12(\epsilon_++\epsilon_-),$$
--
--   $$\epsilon_i=(1-e)D_{ii}+eD_{i,1-i},\qquad\epsilon_{j\,{\rm(Bob)}}=(1-e)D_{jj}+eD_{1-j,j}.$$
--
--   These are exactly (18)–(21), with every imaginary announcement still in Eve's conditioning. The displayed finite mixtures also exhibit their finite supports; no Gaussian overlap formula is assumed.
-- source:
--   Security of coherent state quantum cryptography in the presence of Gaussian noise, arXiv:quant-ph/0608015v4, PDF p. 5, §§IV–V, (18)–(21): constructed conditional pure states and DR/RR ensembles

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P53

open MeasureTheory

open QAlgorithms.Papers.Independent.Dependency50.P39

open scoped ComplexConjugate Matrix

attribute [local instance] Classical.propDecidable

/-- PDF pp.3,5--6, (18)--(21): the projected physical vector is normalized,
and density conditioning gives all displayed Eve mixtures and DR/RR ensembles.
The vectors are computed from the fixed isometry, never chosen from Gram data. -/
theorem eve_ensembles (P : CoherentHeterodyneParameters) (V : GaussianAttack P) :
    (∀ alpha beta : ℂ,
      (∀ k, Summable (fun n : ℕ => conj (coherentKet beta n) *
        V.interaction (coherentKet alpha) (n, k))) ∧
      (∀ k, eveBranch V alpha beta k = branchCoefficient V alpha beta k) ∧
      ‖eveBranch V alpha beta‖ ^ 2 = Real.pi * heterodyneDensity P alpha beta ∧
      0 < ‖eveBranch V alpha beta‖ ∧ ‖eveVector V alpha beta‖ = 1) ∧
    ∀ a b : ℝ × ℝ, 0 ≤ a.1 → 0 ≤ b.1 →
      let e := bitError P a b
      IsDensity (physicalMixture V a b) ∧
      (∀ i, IsDensity (physicalDR V a b i) ∧ IsDensity (physicalRR V a b i)) ∧
      physicalMixture V a b = ((1 / 2 : ℝ) : ℂ) •
        (((1 - e : ℝ) : ℂ) • (physicalDyad V a b false false + physicalDyad V a b true true) +
          (e : ℂ) • (physicalDyad V a b false true + physicalDyad V a b true false)) ∧
      physicalMixture V a b = ((1 / 2 : ℝ) : ℂ) •
        (physicalDR V a b false + physicalDR V a b true) ∧
      physicalMixture V a b = ((1 / 2 : ℝ) : ℂ) •
        (physicalRR V a b false + physicalRR V a b true) ∧
      (∀ i, physicalDR V a b i = ((1 - e : ℝ) : ℂ) • physicalDyad V a b i i +
        (e : ℂ) • physicalDyad V a b i (!i)) ∧
      (∀ j, physicalRR V a b j = ((1 - e : ℝ) : ℂ) • physicalDyad V a b j j +
        (e : ℂ) • physicalDyad V a b (!j) j) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P53

end
