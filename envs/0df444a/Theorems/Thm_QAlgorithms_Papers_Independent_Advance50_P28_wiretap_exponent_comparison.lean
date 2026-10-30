-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P28_wiretap_exponent_comparison
-- name    : QAlgorithms.Papers.Independent.Advance50.P28.wiretap_exponent_comparison
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:55:41.889105+00:00
-- url     : https://prove2.me/theorems/d4ab95dd-c90f-42ed-899d-972ca743b55e
-- title:
--   General wiretap exponent comparison
-- statement:
--   Let $W^B:X\to\operatorname{Prob}(Y)$ and $W^E:X\to\operatorname{Prob}(Z)$ be classical stochastic channels with countable discrete input and measurable output densities, and let $p$ be an input law. Put $J_t(W,p)=\int(\sum_xp(x)W_x(y)^{1/(1-t)})^{1-t}\,dy=\exp\phi(t\mid W,p)$. Codes have normalized stochastic encoders, disjoint measurable decoding sets, uniform messages, average Bob error $\epsilon_B$, and full $L^1$ message–Eve dependence $d_1$ against their actual Eve marginal. For a normalized channel $W$ and every $0\le t\le1/2$, define $\psi(s)=\log\int\sum_xp(x)W_x(y)^{1+s}W_p(y)^{-s}\,dy$, excluding zero-mixture outputs before the negative power. Then
--   $$\phi(t)\le(1-t)\psi\!\left(\frac{t}{1-t}\right),\qquad e_\phi(R)\ge e_\psi(R)\ge\widetilde e_\psi(R),$$
--   where $e_\psi=\sup_{0\le s\le1}(sR-\psi(s))/(1+s)$ and $\widetilde e_\psi=\sup_{0\le s\le1}(sR-\psi(s))/2$. The dominance is non-strict, and extended logarithms handle infinite moments. Here $e_\phi(R)=\sup_{0\le t\le1/2}[tR-\phi(t)]$.
-- source:
--   Tight exponential analysis of universally composable privacy amplification and its applications, arXiv:1010.1358v5, PDF p. 14, General wiretap exponent comparison

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P28

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P28

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Hayashi, PDF pp.13–14: non-strict comparison, including zero-support outputs. -/
theorem wiretap_exponent_comparison {X E : Type*} [Countable X] [Nonempty X]
    [MeasurableSpace E] (mu : Measure E) (W : X → E → ℝ≥0∞)
    (hW : IsDensityChannel mu W) (p : X → ℝ≥0∞) (hp : IsENNRealDiscreteLaw p) (R : ℝ) :
    (∀ t ∈ Set.Icc (0 : ℝ) (1 / 2),
      ENNReal.log (gallagerDensityMoment mu W p t) ≤
        ((1 - t : ℝ) : EReal) * ENNReal.log (psiMoment mu W p (t / (1 - t)))) ∧
    wiretapPsiExponent mu W p R ≤ wiretapPhiExponent mu W p R ∧
    wiretapTildeExponent mu W p R ≤ wiretapPsiExponent mu W p R := by sorry

end QAlgorithms.Papers.Independent.Advance50.P28

end
