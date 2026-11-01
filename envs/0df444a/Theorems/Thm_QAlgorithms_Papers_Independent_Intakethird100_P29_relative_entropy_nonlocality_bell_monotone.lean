-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P29_relative_entropy_nonlocality_bell_monotone
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P29.relative_entropy_nonlocality_bell_monotone
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:08:50.094603+00:00
-- url     : https://prove2.me/theorems/c684890e-a6b8-4c82-8226-970ac7ef8f0f
-- title:
--   Theorem 8: Bell monotonicity of the relative entropy of nonlocality
-- statement:
--   All Bell scenarios have independent finite, nonempty Alice and Bob input and output alphabets. A behavior is a nonnegative conditional output law normalized at every input pair; $\mathrm{NS}$ imposes both no-signaling marginal identities. Processing uses one initial box with rules and randomness fixed independently of the supplied behavior. Write $D(P\Vert Q)$ for classical Kullback–Leibler divergence with natural logarithms, zero numerator contributing zero and positive numerator over zero contributing $+\infty$. Define $S_b(P\Vert Q)=\max_{x,y}D(P(\cdot,\cdot\mid x,y)\Vert Q(\cdot,\cdot\mid x,y))$. For an input law $d$, put $D_d(P\Vert Q)=\sum_{x,y}d(x,y)D(P(\cdot,\cdot\mid x,y)\Vert Q(\cdot,\cdot\mid x,y))$, with zero-weight terms equal to zero. Let $\mathcal L$ be all local-hidden-variable behaviors on the same alphabets. Define $S_{\rm nl}(P)=\min_{Q\in\mathcal L}S_b(P\Vert Q)$, $S_u(P)=\min_{Q\in\mathcal L}D_u(P\Vert Q)$ for the uniform joint law $u$, $S_{uc}(P)=\max_{d_X,d_Y}\min_{Q\in\mathcal L}D_{d_Xd_Y}(P\Vert Q)$, and $S_c(P)=\max_d\min_{Q\in\mathcal L}D_d(P\Vert Q)$ over all joint laws. A Bell nonlocality monotone is a family of finite, nonnegative values on no-signaling behaviors in all scenarios. It vanishes on every local behavior and does not increase under LOSR or WPICC operations, including operations changing alphabet sizes. The relative entropy of nonlocality satisfies
--
--   $$S_{\rm nl}(P)=0\quad(P\in\mathcal L),\qquad S_{\rm nl}(W(P))\le S_{\rm nl}(P)\quad(P\in\mathrm{NS},\ W\in\mathrm{LOSR}\cup\mathrm{WPICC}).$$
--
--   The values are finite and nonnegative. This supplies a nonlocality measure compatible with both free-operation classes. WPICC uses Appendix A’s fixed no-preparation LOSR branch and random adaptive preparation branches in which at least one party measures before the final inputs.
-- source:
--   Nonlocality free wirings and the distinguishability between Bell boxes, arXiv:1611.06932v2, PDF p. 7, Theorem 8

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

/-- PDF p.7, Theorem 8, with Definitions 5 and 7 expanded by the predicates.
Includes vanishing on all local boxes and monotonicity across scenarios. -/
theorem relative_entropy_nonlocality_bell_monotone :
    IsBellMonotone (fun _ p => snl p) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P29

end
