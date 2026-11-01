-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P29_uniform_strength_not_monotone
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P29.uniform_strength_not_monotone
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:09:47.762394+00:00
-- url     : https://prove2.me/theorems/025d6716-9dc7-44ea-99cd-6618d60fdaf0
-- title:
--   Theorem 9: uniform-input statistical strength is not a monotone
-- statement:
--   All Bell scenarios have independent finite, nonempty Alice and Bob input and output alphabets. A behavior is a nonnegative conditional output law normalized at every input pair; $\mathrm{NS}$ imposes both no-signaling marginal identities. Processing uses one initial box with rules and randomness fixed independently of the supplied behavior. Write $D(P\Vert Q)$ for classical Kullback–Leibler divergence with natural logarithms, zero numerator contributing zero and positive numerator over zero contributing $+\infty$. Define $S_b(P\Vert Q)=\max_{x,y}D(P(\cdot,\cdot\mid x,y)\Vert Q(\cdot,\cdot\mid x,y))$. For an input law $d$, put $D_d(P\Vert Q)=\sum_{x,y}d(x,y)D(P(\cdot,\cdot\mid x,y)\Vert Q(\cdot,\cdot\mid x,y))$, with zero-weight terms equal to zero. Let $\mathcal L$ be all local-hidden-variable behaviors on the same alphabets. Define $S_{\rm nl}(P)=\min_{Q\in\mathcal L}S_b(P\Vert Q)$, $S_u(P)=\min_{Q\in\mathcal L}D_u(P\Vert Q)$ for the uniform joint law $u$, $S_{uc}(P)=\max_{d_X,d_Y}\min_{Q\in\mathcal L}D_{d_Xd_Y}(P\Vert Q)$, and $S_c(P)=\max_d\min_{Q\in\mathcal L}D_d(P\Vert Q)$ over all joint laws. There are scenarios, an LOSR wiring $W$, and $P\in\mathrm{NS}$ such that
--
--   $$S_u(W(P))>S_u(P).$$
--
--   Consequently $S_u$ is neither an LOSR monotone, nor a WPICC monotone, nor a Bell nonlocality monotone. This rules out the uniform-input strength as a free-operation monotone. No quantum-realizability hypothesis or specific factor-four witness is part of this statement. WPICC uses Appendix A’s fixed no-preparation LOSR branch and random adaptive preparation branches in which at least one party measures before the final inputs.
-- source:
--   Nonlocality free wirings and the distinguishability between Bell boxes, arXiv:1611.06932v2, PDF p. 8, Theorem 9

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

/-- PDF p.8, Theorem 9, and p.13 opening of Appendix F: a strict LOSR increase
exists, hence all three monotone claims fail. No quantum realization is required.
This states no claim about the inconsistent printed factor-four witness (F10). -/
theorem uniform_strength_not_monotone :
    (∃ (s t : BellScenario) (w : BellOperation s t) (p : Behavior s),
      IsLOSR w ∧ IsNS p ∧ su p < su (w p)) ∧
    ¬ IsLOSRMonotone (fun _ p => su p) ∧
    ¬ IsWPICCMonotone (fun _ p => su p) ∧
    ¬ IsBellMonotone (fun _ p => su p) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P29

end
