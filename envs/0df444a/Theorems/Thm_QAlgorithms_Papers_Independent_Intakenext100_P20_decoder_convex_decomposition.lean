-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P20_decoder_convex_decomposition
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P20.decoder_convex_decomposition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:38:10.684001+00:00
-- url     : https://prove2.me/theorems/1ab8a7f4-27da-4eb0-8888-4209e3d08f43
-- title:
--   Lemma 6, (29): decoder convex decomposition
-- statement:
--   Let $\mathcal K$ and $\mathcal H$ be nonzero finite-dimensional complex Hilbert spaces. Let $\mathcal D$ be the set of CPTP decoders from $\mathcal S(\mathcal K)$ to $\mathcal S(\mathcal H)$, represented by their complex-linear actions on all matrices. Let $\mathcal D_{\rm iso}$ consist of the decoders for which a finite nonzero ancilla $\mathcal H'$ and a vector isometry $V:\mathcal K\to\mathcal H\otimes\mathcal H'$ satisfy $D(\rho)=\operatorname{Tr}_{\mathcal H'}(V\rho V^\dagger)$ for every input state. Then
--
--   $$\mathcal D=\operatorname{conv}_{\mathbb R}(\mathcal D_{\rm iso}).$$
--
--   The ancilla and isometry are fixed before the input state. This is a convex-hull statement, without an assertion that these decoders are precisely the extreme points.
-- source:
--   Exponents of quantum fixed-length pure state source coding, arXiv:quant-ph/0202002v6, PDF p. 5, Lemma 6, (29): decoder convex decomposition

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P20

noncomputable section

open scoped Matrix ENNReal ComplexOrder Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P20

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P47 (IsProbability)

open QAlgorithms.Papers.Independent.Information100.P53 (SpectralData)

open QAlgorithms.Papers.Independent.Gap48.P19 (shannonNats)

open QAlgorithms.Papers.Independent.Dependency50.P28 (classicalD)

attribute [local instance] Classical.propDecidable

/-- Lemma 6, PDF p.5, (29): the decoder set is the real convex hull of
isometric-dilation decoders. No characterization of extreme decoders is asserted. -/
theorem decoder_convex_decomposition (m d : ℕ) (hm : 0 < m) (hd : 0 < d) :
    decoders m d = convexHull ℝ (dilatedDecoders m d) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P20

end
