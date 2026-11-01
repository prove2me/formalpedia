-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P48_quantum_maximum
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P48.quantum_maximum
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:33:35.988687+00:00
-- url     : https://prove2.me/theorems/7723ea42-d2de-4609-bb47-fd28bc75a3c8
-- title:
--   The quantum two-parameter parity maximum is attained at one plus sqrt two
-- statement:
--   For $0\le\varepsilon,\delta\le1$, let $P_{\varepsilon,\delta}$ put probability $(1-r)/2$ on each equal-output pair and $r/2$ on each unequal-output pair, where $r=\varepsilon$ at input $11$ and $r=\delta$ at the other inputs. Let $\operatorname{NL}$ be the maximum of the four absolute CHSH expressions, and let $P_{\varepsilon,\delta}^{(n)}$ be the output of the parallel local-XOR protocol on $n$ independent identical copies. Consider all actual distilled values
--
--   $$
--   S=\left\{\operatorname{NL}(P_{\varepsilon,\delta}^{(n)}):
--   0\le\varepsilon,\delta\le1,\ n>1,\ P_{\varepsilon,\delta}\text{ quantum},
--   \operatorname{NL}(P_{\varepsilon,\delta}^{(n)})>\operatorname{NL}(P_{\varepsilon,\delta})>2\right\}.
--   $$
--
--   Then $S$ has greatest element $1+\sqrt2$. It is attained by
--
--   $$
--   n_{\max}=2,\qquad
--   \delta_{\max}=\frac{1-\cos(\pi/8)}2,\qquad
--   \varepsilon_{\max}=\frac{1-\cos(3\pi/8)}2,
--   $$
--
--   where $0<\delta_{\max}<\varepsilon_{\max}<1/2$, the resource is quantum, and strict distillation holds. These exact parameters correspond to the source's roundings $0.03806$ and $0.30866$. This is an attained maximum for this family and this protocol, not a bound on all quantum distillation protocols.
-- source:
--   Distilling Non-Locality, arXiv:0809.3173v4, PDF p. 4, Unnumbered: attained maximum for the quantum two-parameter family

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P48

namespace QAlgorithms.Papers.Independent.Intakethird100.P48

open scoped BigOperators TensorProduct

noncomputable section

/-- PDF p.4, attained maximum: 1+sqrt(2) for this quantum two-parameter family
and NDP, with n=2 at the displayed optimizer. The CHSH maximum is used throughout
the full positivity square; 3(1-2delta)^n-(1-2epsilon)^n is not used outside its sector.
The cosine coordinates identify exactly the source's rounded parameter values.
Printed/changed/why: the source's signed scalar formula is sector-specific;
Definition 1's actual absolute maximum replaces it on the full positivity square
(epsilon=delta=1 has actual NL=2, whereas the printed signed expression is -2).
Independent moderation of this transcription choice remains pending. -/
theorem quantum_maximum :
    IsGreatest quantumDistilledValues (1 + Real.sqrt 2) ∧
    0 < optimalDelta ∧ optimalDelta < optimalEpsilon ∧ optimalEpsilon < 1 / 2 ∧
    IsQuantum (parameterBox optimalEpsilon optimalDelta) ∧
    StrictlyDistills (parityProtocol 2) (parameterBox optimalEpsilon optimalDelta) ∧
    nonlocality (parallelOutputLaw (parityProtocol 2) (parameterBox optimalEpsilon optimalDelta)) =
      1 + Real.sqrt 2 := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P48
