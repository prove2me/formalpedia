-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P29_product_strength_bell_monotone
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P29.product_strength_bell_monotone
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:10:26.151091+00:00
-- url     : https://prove2.me/theorems/b0d31534-ed5c-40a3-bcdc-c58cc4917915
-- title:
--   Theorem 10: product-input statistical strength is a Bell monotone
-- statement:
--   All Bell scenarios have independent finite, nonempty Alice and Bob input and output alphabets. A behavior is a nonnegative conditional output law normalized at every input pair; $\mathrm{NS}$ imposes both no-signaling marginal identities. Processing uses one initial box with rules and randomness fixed independently of the supplied behavior. Write $D(P\Vert Q)$ for classical Kullback–Leibler divergence with natural logarithms, zero numerator contributing zero and positive numerator over zero contributing $+\infty$. Define $S_b(P\Vert Q)=\max_{x,y}D(P(\cdot,\cdot\mid x,y)\Vert Q(\cdot,\cdot\mid x,y))$. For an input law $d$, put $D_d(P\Vert Q)=\sum_{x,y}d(x,y)D(P(\cdot,\cdot\mid x,y)\Vert Q(\cdot,\cdot\mid x,y))$, with zero-weight terms equal to zero. Let $\mathcal L$ be all local-hidden-variable behaviors on the same alphabets. Define $S_{\rm nl}(P)=\min_{Q\in\mathcal L}S_b(P\Vert Q)$, $S_u(P)=\min_{Q\in\mathcal L}D_u(P\Vert Q)$ for the uniform joint law $u$, $S_{uc}(P)=\max_{d_X,d_Y}\min_{Q\in\mathcal L}D_{d_Xd_Y}(P\Vert Q)$, and $S_c(P)=\max_d\min_{Q\in\mathcal L}D_d(P\Vert Q)$ over all joint laws. A Bell nonlocality monotone is a family of finite, nonnegative values on no-signaling behaviors in all scenarios. It vanishes on every local behavior and does not increase under LOSR or WPICC operations, including operations changing alphabet sizes. The product-input strength is finite, vanishes on local behaviors, and satisfies
--
--   $$S_{uc}(W(P))\le S_{uc}(P)\quad(P\in\mathrm{NS},\ W\in\mathrm{LOSR}\cup\mathrm{WPICC}).$$
--
--   Thus $S_{uc}$ is a Bell nonlocality monotone. The local comparison class is $\mathcal L$; the quantum-comparison variant is not covered. WPICC uses Appendix A’s fixed no-preparation LOSR branch and random adaptive preparation branches in which at least one party measures before the final inputs.
-- source:
--   Nonlocality free wirings and the distinguishability between Bell boxes, arXiv:1611.06932v2, PDF p. 8, Theorem 10

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

/-- PDF p.8, Theorem 10, proved on pp.14–15: (22b), with local comparison boxes.
The quantum-comparison variant of (24) is not asserted to be monotone. -/
theorem product_strength_bell_monotone :
    IsBellMonotone (fun _ p => suc p) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P29

end
