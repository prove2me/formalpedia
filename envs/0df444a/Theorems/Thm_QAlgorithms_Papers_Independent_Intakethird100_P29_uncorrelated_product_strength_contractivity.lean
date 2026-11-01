-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P29_uncorrelated_product_strength_contractivity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P29.uncorrelated_product_strength_contractivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:11:50.793731+00:00
-- url     : https://prove2.me/theorems/eb5de6d8-9d0f-4944-adf9-5583fdcb5ca9
-- title:
--   Lemma 12 (G2): UCLOSR monotonicity of Suc
-- statement:
--   All Bell scenarios have independent finite, nonempty Alice and Bob input and output alphabets. A behavior is a nonnegative conditional output law normalized at every input pair; $\mathrm{NS}$ imposes both no-signaling marginal identities. Processing uses one initial box with rules and randomness fixed independently of the supplied behavior. Write $D(P\Vert Q)$ for classical Kullback–Leibler divergence with natural logarithms, zero numerator contributing zero and positive numerator over zero contributing $+\infty$. Define $S_b(P\Vert Q)=\max_{x,y}D(P(\cdot,\cdot\mid x,y)\Vert Q(\cdot,\cdot\mid x,y))$. For an input law $d$, put $D_d(P\Vert Q)=\sum_{x,y}d(x,y)D(P(\cdot,\cdot\mid x,y)\Vert Q(\cdot,\cdot\mid x,y))$, with zero-weight terms equal to zero. Let $\mathcal L$ be all local-hidden-variable behaviors on the same alphabets. Define $S_{\rm nl}(P)=\min_{Q\in\mathcal L}S_b(P\Vert Q)$, $S_u(P)=\min_{Q\in\mathcal L}D_u(P\Vert Q)$ for the uniform joint law $u$, $S_{uc}(P)=\max_{d_X,d_Y}\min_{Q\in\mathcal L}D_{d_Xd_Y}(P\Vert Q)$, and $S_c(P)=\max_d\min_{Q\in\mathcal L}D_d(P\Vert Q)$ over all joint laws. For every no-signaling behavior $P$ and every UCLOSR wiring $U$, whose input and output kernels are products of four normalized one-party kernels,
--
--   $$S_{uc}(U(P))\le S_{uc}(P).$$
--
--   The component wiring itself has no shared hidden variable. This is the uncorrelated component monotonicity used in the LOSR decomposition.
-- source:
--   Nonlocality free wirings and the distinguishability between Bell boxes, arXiv:1611.06932v2, PDF p. 15, Lemma 12 (G2)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P29

noncomputable section

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intakethird100.P29

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Advance50.P47
  (Box IsCorrelation IsNoSignaling HasLocalModel TwoLocalBoxes losrTransform
   correlationMixture)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Dependency50.P47 (Law)

/-- PDF p.15, Lemma 12, (G2): four independent local kernels, with arbitrary
initial and final finite nonempty alphabets. -/
theorem uncorrelated_product_strength_contractivity {s t : BellScenario}
    (u : UncorrelatedWiring s t) (p : Behavior s) (hp : IsNS p) :
    suc (u.apply p) ≤ suc p := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P29

end
