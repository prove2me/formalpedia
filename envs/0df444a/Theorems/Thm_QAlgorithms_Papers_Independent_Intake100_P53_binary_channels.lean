-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P53_binary_channels
-- name    : QAlgorithms.Papers.Independent.Intake100.P53.binary_channels
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:45:19.58899+00:00
-- url     : https://prove2.me/theorems/94e6f564-362a-4f6d-8540-53104e08fa67
-- title:
--   §V, (6)–(12),(16)–(17): announcement-induced symmetric binary channels
-- statement:
--   Let $\kappa>0$, $0<\eta\le1$, and $\delta\ge0$ be finite real parameters. Alice modulates normalized oscillator coherent states with density $\exp(-|\alpha|^2/(2\kappa))/(2\pi\kappa)$ relative to planar Lebesgue measure. Bob's tomographically verified output is $D(\sqrt\eta\alpha)\tau_{\delta/2}D(\sqrt\eta\alpha)^\dagger$, where $\tau_n$ is the thermal state of mean photon number $n$, and he uses ideal heterodyne detection. Bits are the signs of the real parts, with bit zero for a nonnegative real part. Public announcements are $a=(u,y)=(|\Re\alpha|,\Im\alpha)$ and $b=(w,z)=(|\Re\beta|,\Im\beta)$. Zero-real-part events have probability zero. All formulas below concern the source's collective-attack, infinite-key setting with completed tomography; they assert no finite-sample or coherent-attack security.
--
--   Construct the joint modulation/outcome law using the Gaussian conditional law (5), and let $P_{\rm ann}$ be its pushforward by the announcement maps. For $i,j\in\{0,1\}$ set $\alpha_i=(-1)^i u+\mathrm{i}y$ and $\beta_j=(-1)^j w+\mathrm{i}z$. Define the positive density $d_{ij}=p(\alpha_i)p(\beta_j\mid\alpha_i)$, $p_{\rm ann}=\sum_{ij}d_{ij}$, and the density kernel $K_{ij}=d_{ij}/p_{\rm ann}$. On $u,w\ge0$, the actual crossover probability $e=\sum_i K_{i,1-i}$ satisfies
--
--   $$e(u,w)=\frac1{1+\exp(8\sqrt\eta\,uw/(2+\delta))},\qquad K_{ij}=\frac12\begin{cases}1-e,&i=j,\\e,&i\ne j.\end{cases}$$
--
--   Both bit marginals are uniform and $0\le e\le1/2$. The measure $P_{\rm ann}$ has density $p_{\rm ann}=p(a)p(b\mid a)$ on the two half-planes and zero outside. Here $p(a)=\exp(-(u^2+y^2)/(2\kappa))/(\pi\kappa)$. Integrating the imaginary coordinates gives
--
--   $$p_U(u)=\sqrt{\frac2{\pi\kappa}}e^{-u^2/(2\kappa)},\quad p_{W\mid U}(w\mid u)=\sqrt{\frac2{\pi(2+\delta)}}\left[e^{-2(w+\sqrt\eta u)^2/(2+\delta)}+e^{-2(w-\sqrt\eta u)^2/(2+\delta)}\right].$$
--
--   The kernel extends continuously with $e=1/2$ on the null axes. This decomposes each distributed signal into the source's effective symmetric binary channel without conditioning on a probability-zero singleton.
-- source:
--   Security of coherent state quantum cryptography in the presence of Gaussian noise, arXiv:quant-ph/0608015v4, PDF p. 4, §V, (6)–(12),(16)–(17): announcement-induced symmetric binary channels

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P53

open MeasureTheory

open QAlgorithms.Papers.Independent.Dependency50.P39

open scoped ComplexConjugate Matrix

attribute [local instance] Classical.propDecidable

/-- PDF pp.4--5, V, (6)--(12),(16)--(17): the induced public law, uniform
sign marginals, symmetric conditional channel, logistic error and marginal
densities. Axis values are the continuous extension; null-axis duplicate sign
labels are not positive mass in the pushforward-measure identity. -/
theorem binary_channels (P : CoherentHeterodyneParameters) :
    announcementLaw P = (volume : Measure ((ℝ × ℝ) × (ℝ × ℝ))).withDensity
      (fun z => ENNReal.ofReal
        (if 0 ≤ z.1.1 ∧ 0 ≤ z.2.1 then announcementDensity P z.1 z.2 else 0)) ∧
    ∀ (a b : ℝ × ℝ), 0 ≤ a.1 → 0 ≤ b.1 →
      0 < announcementDensity P a b ∧
      bitError P a b = 1 / (1 + Real.exp (8 * Real.sqrt P.eta * a.1 * b.1 / (2 + P.delta))) ∧
      0 ≤ bitError P a b ∧ bitError P a b ≤ 1 / 2 ∧
      (∀ i j : Bool, signKernel P a b i j =
        (if i = j then 1 - bitError P a b else bitError P a b) / 2) ∧
      (∀ i : Bool, (∑ j : Bool, signKernel P a b i j) = 1 / 2 ∧
        (∑ j : Bool, signKernel P a b j i) = 1 / 2) ∧
      aliceAnnouncementDensity P a =
        Real.exp (-(a.1 ^ 2 + a.2 ^ 2) / (2 * P.kappa)) / (Real.pi * P.kappa) ∧
      announcementDensity P a b = aliceAnnouncementDensity P a * bobAnnouncementDensity P a b ∧
      (∫ y : ℝ, aliceAnnouncementDensity P (a.1, y)) = aliceMagnitudeDensity P a.1 ∧
      (∫ y : ℝ, bobAnnouncementDensity P a (b.1, y)) = bobMagnitudeDensity P a.1 b.1 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P53

end
