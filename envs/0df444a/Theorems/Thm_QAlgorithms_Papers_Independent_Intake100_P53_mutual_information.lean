-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P53_mutual_information
-- name    : QAlgorithms.Papers.Independent.Intake100.P53.mutual_information
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:46:10.725785+00:00
-- url     : https://prove2.me/theorems/87ad81b0-3e88-4869-a334-9589c22847ae
-- title:
--   §V, (13)–(17): averaged mutual information of effective channels
-- statement:
--   Let $\kappa>0$, $0<\eta\le1$, and $\delta\ge0$ be finite real parameters. Alice modulates normalized oscillator coherent states with density $\exp(-|\alpha|^2/(2\kappa))/(2\pi\kappa)$ relative to planar Lebesgue measure. Bob's tomographically verified output is $D(\sqrt\eta\alpha)\tau_{\delta/2}D(\sqrt\eta\alpha)^\dagger$, where $\tau_n$ is the thermal state of mean photon number $n$, and he uses ideal heterodyne detection. Bits are the signs of the real parts, with bit zero for a nonnegative real part. Public announcements are $a=(u,y)=(|\Re\alpha|,\Im\alpha)$ and $b=(w,z)=(|\Re\beta|,\Im\beta)$. Zero-real-part events have probability zero. All formulas below concern the source's collective-attack, infinite-key setting with completed tomography; they assert no finite-sample or coherent-attack security.
--
--   Let $K_{ij}(a,b)$ be the conditional sign kernel obtained from the four joint density preimages, and let $P_{\rm ann}$ be the actual induced announcement law. Compute $I(a,b)=\sum_{ij}K_{ij}\log_2(K_{ij}/(K_{i\bullet}K_{\bullet j}))$ from its row and column marginals. With $h_2$ the binary entropy in bits and $e$ the actual conditional bit error, $I(a,b)=1-h_2(e(a,b))$. This function is integrable and
--
--   $$I_{A:B}=\int I(a,b)\,dP_{\rm ann}=\int_0^\infty\!du\int_{\mathbb R}\!dy\int_0^\infty\!dw\int_{\mathbb R}\!dz\;p_{\rm ann}((u,y),(w,z))[1-h_2(e)]$$
--
--   $$=\int_0^\infty p_U(u)\int_0^\infty p_{W\mid U}(w\mid u)[1-h_2(e(u,w))]\,dw\,du,\qquad0\le I_{A:B}\le1.$$
--
--   Here $p_U$ and $p_{W\mid U}$ are precisely the half-normal and folded-normal densities (17) and (16). The imaginary announcements can be integrated out of this classical quantity because the error depends only on $u,w$. This result concerns the mutual information of the announced sign channels, not the unconditional analog amplitudes.
-- source:
--   Security of coherent state quantum cryptography in the presence of Gaussian noise, arXiv:quant-ph/0608015v4, PDF p. 4, §V, (13)–(17): averaged mutual information of effective channels

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P53

open MeasureTheory

open QAlgorithms.Papers.Independent.Dependency50.P39

open scoped ComplexConjugate Matrix

attribute [local instance] Classical.propDecidable

/-- PDF pp.4--5, V, (13)--(17): an integral identity, not mere existence.
Imaginary announcements integrate out because the error ignores them.
Bounded conditional MI and genuine integrability are conclusions. -/
theorem mutual_information (P : CoherentHeterodyneParameters) :
    Integrable (fun z => channelMutualInformation P z.1 z.2) (announcementLaw P) ∧
    (∀ a b : ℝ × ℝ, 0 ≤ a.1 → 0 ≤ b.1 →
      channelMutualInformation P a b = 1 - QAlgorithms.binEntropy2 (bitError P a b)) ∧
    announcedMutualInformation P =
      (∫ u in Set.Ioi (0 : ℝ), ∫ y : ℝ, ∫ w in Set.Ioi (0 : ℝ), ∫ z : ℝ,
        announcementDensity P (u, y) (w, z) *
          (1 - QAlgorithms.binEntropy2 (bitError P (u, y) (w, z)))) ∧
    announcedMutualInformation P =
      (∫ u in Set.Ioi (0 : ℝ), ∫ w in Set.Ioi (0 : ℝ),
        aliceMagnitudeDensity P u * bobMagnitudeDensity P u w *
          (1 - QAlgorithms.binEntropy2 (bitError P (u, 0) (w, 0)))) ∧
    0 ≤ announcedMutualInformation P ∧ announcedMutualInformation P ≤ 1 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P53

end
