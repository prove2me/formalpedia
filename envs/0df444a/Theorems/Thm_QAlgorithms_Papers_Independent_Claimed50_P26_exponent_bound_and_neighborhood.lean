-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P26_exponent_bound_and_neighborhood
-- name    : QAlgorithms.Papers.Independent.Claimed50.P26.exponent_bound_and_neighborhood
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:58:55.764975+00:00
-- url     : https://prove2.me/theorems/2c893a34-48c8-48c0-b18a-ed449d430870
-- title:
--   Lemma I.2 (both parts and the stated consequence)
-- statement:
--   Let $\Phi$ be any channel on nonzero finite-dimensional input and output spaces. Write $\chi_\alpha^*(\Phi)$ for its maximum ensemble Rényi–Holevo information, $\bar\chi_\alpha^*(\Phi)$ for its regularization, and $\chi^*(\Phi)=\chi_1^*(\Phi)$. Let $E^\Phi(R)$ be the liminf of $-\log_2 P_{\rm succ}^{\rm opt}(n,R)/n$, with $-\log_2 0=+\infty$ and integer message counts $\lceil2^{nR}\rceil$. Then
--
--   $$
--   E^\Phi(R)\ge (1-1/\alpha)\bigl(R-\bar\chi_\alpha^*(\Phi)\bigr)
--   \quad(R\ge0,\ \alpha>1).
--   $$
--
--   For every $R>\chi^*(\Phi)$ there is a $\beta=\beta(\Phi,R)>1$ such that $\chi_\alpha^*(\Phi)<R$ for every $1<\alpha<\beta$. In particular, if $\chi_\alpha^*(\Phi^{\otimes n})=n\chi_\alpha^*(\Phi)$ for every positive $n$ at all orders in some neighborhood above one, then $E^\Phi(R)>0$ for every $R>\chi^*(\Phi)$. The neighborhood is uniform over all finite ensembles. This relates optimal unassisted coding exponents to information quantities without covariance assumptions.
-- source:
--   A strong converse for classical channel coding using entangled inputs, arXiv:0903.2838v1, PDF p. 5, Lemma I.2 (both parts and the stated consequence)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P26

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate Topology

open Filter

namespace QAlgorithms.Papers.Independent.Claimed50.P26

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage depolarizing)

open QAlgorithms.Papers.Independent.Information100.P71
  (supportPower channelPower)

open QAlgorithms.Papers.Independent.Dependency50.P23
  (UACode uaCodeSuccess uaSuccess ordinaryClassicalCapacity)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Dependency50.P35 (renyiEntropy petz relative)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)

/-- PDF p.5, Lemma I.2, both parts and consequence; finite-block proof on p.9.
The factor (1-1/alpha) multiplies the entire rate gap. No covariance is assumed. -/
theorem exponent_bound_and_neighborhood {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (Phi : Superop I J) (hPhi : IsChannel Phi) :
    (∀ R : ℝ, 0 ≤ R → ∀ alpha : ℝ, 1 < alpha →
      (((1-1/alpha)*(R-regularizedChi alpha Phi) : ℝ) : EReal) ≤ unassistedCodingExponent Phi R) ∧
    (∀ R : ℝ, channelChi 1 Phi < R → ∃ beta : ℝ, 1 < beta ∧
      ∀ alpha : ℝ, 1 < alpha → alpha < beta → channelChi alpha Phi < R) ∧
    (LocalChiAdditive Phi → ∀ R : ℝ, channelChi 1 Phi < R → 0 < unassistedCodingExponent Phi R) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P26

end
