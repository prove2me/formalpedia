-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P46_gaussianReliabilityRegimes
-- name    : QAlgorithms.Papers.Independent.Renew46.P46.gaussianReliabilityRegimes
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:59:45.266483+00:00
-- url     : https://prove2.me/theorems/37e7963e-3650-43b4-8b5b-cc0075923921
-- title:
--   §V: fixed-Gaussian reliability lower bounds and three exponent regimes
-- statement:
--   Fix $E>0$ and $0<R<h(E)$ for the noiseless coherent-state channel, where $h(E)=(E+1)\log(E+1)-E\log E$. Keep the prior fixed to $G_E$. Let $E_r^G(R)$ be the supremum of $\mu_E(s,p)-sR$ over $0\le s\le1$, $0\le p<1/E$, and let $E_{\rm ex}^G(R)$ be the supremum of $\widetilde\mu_E(s,p)-sR$ over $s\ge1$ and the same $p$ domain. Write $q=(1+\sqrt{1+4E^2})/2$, $L=\log q$, $A=2(E+1-q)+\log q$, and $B=E+1-q+(q^2\log q-E^2\log E)/(q^2-E^2)$. The actual extended reliability $\mathcal E(R)=\limsup_n[-\log p(n,M_n)]/n$, with zero error interpreted as $+\infty$ and $M_n=\max(1,\lfloor e^{nR}\rfloor)$, satisfies
--
--   $$\mathcal E(R)\ge\max\{E_r^G(R),E_{\rm ex}^G(R)\}.$$
--
--   For $R<L$, the stationary $s=E/\sqrt{e^{2R}-e^R}$ is greater than one and
--
--   $$E_{\rm ex}^G(R)=2E(1-\sqrt{1-e^{-R}})>E_r^G(R).$$
--
--   For $L\le R\le B$, both envelopes equal $A-R$. For $B<R<h(E)$, $E_{\rm ex}^G(R)<E_r^G(R)$, with the random envelope left as its defined optimization.
--
--   This corrects the printed 'less than 1' using the source's own formula. It concerns a fixed Gaussian prior, not unrestricted optimization over all input laws.
-- source:
--   On Quantum Communication Channels with Constrained Inputs, arXiv:quant-ph/9705054v1, PDF p. 15, §V: fixed-Gaussian reliability lower bounds and three exponent regimes

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P46

open Filter MeasureTheory QAlgorithms.RealRegisters

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Section V, PDF pp.13-15: all three fixed-Gaussian exponent regimes and a
lower bound on the actual reliability. Source correction: p.15 prints "less
than 1" for (46); the formula and R<log q(E) give GREATER than 1. Printed,
changed and reason are recorded in MODERATION_NOTES (trap 30). This is not
the defective unrestricted-prior reliability claim (40)-(41). -/
theorem gaussianReliabilityRegimes (E R : ℝ) (hE : 0 < E)
    (hR : 0 < R) (hRC : R < h E) :
    ∃ hS : ∀ alpha, constrainedCqDensity (gaussianSignal 0 alpha),
      ((max (randomEnvelope E R) (expurgatedEnvelope E R) : ℝ) : EReal) ≤
        reliability (stateFamily (gaussianSignal 0) hS) energyCost E R ∧
      (R < Lvalue E →
        1 < E / Real.sqrt (Real.exp (2 * R) - Real.exp R) ∧
        expurgatedEnvelope E R = 2 * E * (1 - Real.sqrt (1 - Real.exp (-R))) ∧
        randomEnvelope E R < expurgatedEnvelope E R) ∧
      (Lvalue E ≤ R → R ≤ Bvalue E →
        expurgatedEnvelope E R = Avalue E - R ∧
        randomEnvelope E R = Avalue E - R) ∧
      (Bvalue E < R → expurgatedEnvelope E R < randomEnvelope E R) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P46

end
