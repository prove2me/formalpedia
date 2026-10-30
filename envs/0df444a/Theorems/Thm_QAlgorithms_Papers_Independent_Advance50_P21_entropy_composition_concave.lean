-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P21_entropy_composition_concave
-- name    : QAlgorithms.Papers.Independent.Advance50.P21.entropy_composition_concave
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:56:38.244501+00:00
-- url     : https://prove2.me/theorems/2863fb9c-96f7-4436-93ec-99e5f0e9e1ca
-- title:
--   Lemma 14: differential sufficient condition for entropy-composition concavity
-- statement:
--   Let $d\ge1$, $c\ge0$, and let $h:\mathbb R\to\mathbb R$ be twice differentiable and nondecreasing. For each probability vector $q=(q_i)_{i=1}^d$, define $H(q)=-\sum_iq_i\log q_i$, $L(q)=\sum_iq_i(\log q_i)^2$ and $V(q)=L(q)-H(q)^2$, with continuous zero-weight terms. If, for every such $q$,
--   $$c\,h''(cH(q))V(q)\le h'(cH(q)),$$
--   then the state function
--   $$\rho\longmapsto h(cH(\rho))$$
--   is concave on all normalized $d$-dimensional states, where $H(\rho)$ is von Neumann entropy in nats. This is the sufficient entropy-composition criterion with the proof's division-free boundary reading; no continuous second derivative or full rank is required.
-- source:
--   Entropy power inequalities for qudits, arXiv:1503.04213v3, PDF p. 16, Lemma 14: differential sufficient condition for entropy-composition concavity

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P21

open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)

open QAlgorithms.Papers.Independent.Dependency50.P16 (simplex orderedSpectrum majorizedBy)

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble)

open QAlgorithms.Papers.Independent.Information100.P49 (thermalEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P11 (thermalEntropyInverse)

/-- PDF p.16, Lemma 14; boundary reading from p.18, (6.17).
Printed (6.3) divides by h' and by V=L-H^2; changed to c*h''*V <= h'.
This retains uniform-on-support distributions, vanishing h', and c=0 without junk division.
Twice differentiable means differentiable h and differentiable h', not C^2. -/
theorem entropy_composition_concave {d : ℕ} (hd : 0 < d) (h : ℝ → ℝ)
    (hh : Differentiable ℝ h) (hhderiv : Differentiable ℝ (deriv h))
    (hmono : Monotone h) (c : ℝ) (hc : 0 ≤ c)
    (hcriterion : ∀ q ∈ simplex d,
      c * deriv (deriv h) (c * simplexShannonNats q) * simplexInformationVariance q ≤
        deriv h (c * simplexShannonNats q)) :
    StateConcave (fun rho : Mat d => h (c * entropy rho)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P21

end
