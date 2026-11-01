-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P29_product_strength_convex
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P29.product_strength_convex
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:13:04.360188+00:00
-- url     : https://prove2.me/theorems/4e6f578b-150a-4aac-973b-cab9e201bc3b
-- title:
--   Lemma 14 (G4): convexity of Suc
-- statement:
--   All Bell scenarios have independent finite, nonempty Alice and Bob input and output alphabets. A behavior is a nonnegative conditional output law normalized at every input pair; $\mathrm{NS}$ imposes both no-signaling marginal identities. Processing uses one initial box with rules and randomness fixed independently of the supplied behavior. Write $D(P\Vert Q)$ for classical Kullback–Leibler divergence with natural logarithms, zero numerator contributing zero and positive numerator over zero contributing $+\infty$. Define $S_b(P\Vert Q)=\max_{x,y}D(P(\cdot,\cdot\mid x,y)\Vert Q(\cdot,\cdot\mid x,y))$. For an input law $d$, put $D_d(P\Vert Q)=\sum_{x,y}d(x,y)D(P(\cdot,\cdot\mid x,y)\Vert Q(\cdot,\cdot\mid x,y))$, with zero-weight terms equal to zero. Let $\mathcal L$ be all local-hidden-variable behaviors on the same alphabets. Define $S_{\rm nl}(P)=\min_{Q\in\mathcal L}S_b(P\Vert Q)$, $S_u(P)=\min_{Q\in\mathcal L}D_u(P\Vert Q)$ for the uniform joint law $u$, $S_{uc}(P)=\max_{d_X,d_Y}\min_{Q\in\mathcal L}D_{d_Xd_Y}(P\Vert Q)$, and $S_c(P)=\max_d\min_{Q\in\mathcal L}D_d(P\Vert Q)$ over all joint laws. For $P,Q\in\mathrm{NS}$ on the same scenario and every real $0\le\mu\le1$,
--
--   $$S_{uc}(\mu P+(1-\mu)Q)\le\mu S_{uc}(P)+(1-\mu)S_{uc}(Q).$$
--
--   This is convexity in the behavior. The product-input maximum remains outside the local minimum; no minimax over the nonconvex set of product laws is asserted.
-- source:
--   Nonlocality free wirings and the distinguishability between Bell boxes, arXiv:1611.06932v2, PDF p. 15, Lemma 14 (G4)

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

/-- PDF p.15, Lemma 14, (G4). Convexity in the behavior, with the product-law
maximum still outside the local minimum; no product-law minimax is used. -/
theorem product_strength_convex {s : BellScenario}
    (p q : Behavior s) (hp : IsNS p) (hq : IsNS q)
    (mu : ℝ) (hmu0 : 0 ≤ mu) (hmu1 : mu ≤ 1) :
    suc (correlationMixture p q mu) ≤
      ENNReal.ofReal mu * suc p + ENNReal.ofReal (1 - mu) * suc q := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P29

end
