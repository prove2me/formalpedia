-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P29_relative_entropy_nonlocality_convex
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P29.relative_entropy_nonlocality_convex
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:11:12.512444+00:00
-- url     : https://prove2.me/theorems/787846e7-911e-4779-b640-3f9ff719adb3
-- title:
--   Lemma 11 (D1): convexity of Snl
-- statement:
--   All Bell scenarios have independent finite, nonempty Alice and Bob input and output alphabets. A behavior is a nonnegative conditional output law normalized at every input pair; $\mathrm{NS}$ imposes both no-signaling marginal identities. Processing uses one initial box with rules and randomness fixed independently of the supplied behavior. Write $D(P\Vert Q)$ for classical Kullback–Leibler divergence with natural logarithms, zero numerator contributing zero and positive numerator over zero contributing $+\infty$. Define $S_b(P\Vert Q)=\max_{x,y}D(P(\cdot,\cdot\mid x,y)\Vert Q(\cdot,\cdot\mid x,y))$. For an input law $d$, put $D_d(P\Vert Q)=\sum_{x,y}d(x,y)D(P(\cdot,\cdot\mid x,y)\Vert Q(\cdot,\cdot\mid x,y))$, with zero-weight terms equal to zero. Let $\mathcal L$ be all local-hidden-variable behaviors on the same alphabets. Define $S_{\rm nl}(P)=\min_{Q\in\mathcal L}S_b(P\Vert Q)$, $S_u(P)=\min_{Q\in\mathcal L}D_u(P\Vert Q)$ for the uniform joint law $u$, $S_{uc}(P)=\max_{d_X,d_Y}\min_{Q\in\mathcal L}D_{d_Xd_Y}(P\Vert Q)$, and $S_c(P)=\max_d\min_{Q\in\mathcal L}D_d(P\Vert Q)$ over all joint laws. For two no-signaling behaviors $P,Q$ on the same scenario and every real $0\le\mu\le1$, their pointwise mixture satisfies
--
--   $$S_{\rm nl}(\mu P+(1-\mu)Q)\le\mu S_{\rm nl}(P)+(1-\mu)S_{\rm nl}(Q).$$
--
--   This is convexity in the behavior, including both endpoints. All optimizing local behaviors are selected by the defining minimization, not supplied as hypotheses.
-- source:
--   Nonlocality free wirings and the distinguishability between Bell boxes, arXiv:1611.06932v2, PDF p. 13, Lemma 11 (D1)

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

/-- PDF p.13, Lemma 11, (D1). The mixture is computed pointwise and both
endpoints of the mixing interval are included. -/
theorem relative_entropy_nonlocality_convex {s : BellScenario}
    (p q : Behavior s) (hp : IsNS p) (hq : IsNS q)
    (mu : ℝ) (hmu0 : 0 ≤ mu) (hmu1 : mu ≤ 1) :
    snl (correlationMixture p q mu) ≤
      ENNReal.ofReal mu * snl p + ENNReal.ofReal (1 - mu) * snl q := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P29

end
