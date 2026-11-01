-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P29_nonlocality_equals_correlated_strength
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P29.nonlocality_equals_correlated_strength
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:16:34.785728+00:00
-- url     : https://prove2.me/theorems/90d9584e-7846-4ff9-8d69-f38de1bf2649
-- title:
--   Unnumbered result (23), (E1): Snl equals Sc
-- statement:
--   All Bell scenarios have independent finite, nonempty Alice and Bob input and output alphabets. A behavior is a nonnegative conditional output law normalized at every input pair; $\mathrm{NS}$ imposes both no-signaling marginal identities. Processing uses one initial box with rules and randomness fixed independently of the supplied behavior. Write $D(P\Vert Q)$ for classical Kullback–Leibler divergence with natural logarithms, zero numerator contributing zero and positive numerator over zero contributing $+\infty$. Define $S_b(P\Vert Q)=\max_{x,y}D(P(\cdot,\cdot\mid x,y)\Vert Q(\cdot,\cdot\mid x,y))$. For an input law $d$, put $D_d(P\Vert Q)=\sum_{x,y}d(x,y)D(P(\cdot,\cdot\mid x,y)\Vert Q(\cdot,\cdot\mid x,y))$, with zero-weight terms equal to zero. Let $\mathcal L$ be all local-hidden-variable behaviors on the same alphabets. Define $S_{\rm nl}(P)=\min_{Q\in\mathcal L}S_b(P\Vert Q)$, $S_u(P)=\min_{Q\in\mathcal L}D_u(P\Vert Q)$ for the uniform joint law $u$, $S_{uc}(P)=\max_{d_X,d_Y}\min_{Q\in\mathcal L}D_{d_Xd_Y}(P\Vert Q)$, and $S_c(P)=\max_d\min_{Q\in\mathcal L}D_d(P\Vert Q)$ over all joint laws. For every no-signaling behavior $P$,
--
--   $$S_{\rm nl}(P)=S_c(P).$$
--
--   All four strengths are finite. The local minimum defining $S_{\rm nl}$, every fixed-input-law local minimum, the uniform-input local minimum, and the outer maxima defining $S_{uc}$ and $S_c$ are attained. The identity uses all joint input laws and extends to local boxes, where both sides vanish. This is the equality credited to van Dam, Grunwald and Gill [24] and explicitly reproved in Appendix E.
-- source:
--   Nonlocality free wirings and the distinguishability between Bell boxes, arXiv:1611.06932v2, PDF p. 8, Equation (23); Appendix E (E1)

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

/-- PDF p.8, (23), and p.13, Appendix E, (E1), credited there to [24].
The source's minima/maxima are explicitly attained and finite. The identity uses
all joint input laws; product-law maximum and local minimum are never swapped.
The same formulas include the zero local case. -/
theorem nonlocality_equals_correlated_strength {s : BellScenario} (p : Behavior s)
    (hp : IsNS p) : OptimaAttained p ∧ snl p = correlatedInputStrength p := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P29

end
