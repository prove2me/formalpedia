-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P77_additive_classical_failure
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P77.additive_classical_failure
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:08:24.927107+00:00
-- url     : https://prove2.me/theorems/1ab5d19b-cf4b-4f35-9076-5b7b2b5f78c4
-- title:
--   Additive classical-failure probability
-- statement:
--   Consider a normalized finite probability experiment with a classical failure event $F$ and bad-security events $B_0,B_1$ for the ideal and faulty classical executions. Assume $B_0$ and $B_1$ agree outside $F$. If $\Pr[B_0]\le p_{\mathrm{luck}}$ and $\Pr[F]\le p_{\mathrm{fail}}$, then
--
--   $$\Pr[B_1]\le p_{\mathrm{luck}}+p_{\mathrm{fail}}.$$
--
--   This is the event comparison meant by adding classical transmission failure to the security failure probability. It introduces neither an unauthenticated-channel claim nor a composable replacement theorem.
-- source:
--   A Proof of the Security of Quantum Key Distribution, arXiv:quant-ph/9912053v1, PDF p. 31, Appendix A / O: additive classical-failure probability

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P77

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P77

open scoped BigOperators ComplexConjugate ComplexOrder

open QAlgorithms

-- The repair instruction authorizes imports of pinned accepted definitions.
-- These are definitions only; no imported paper theorem is used here.

open QAlgorithms.Papers.Independent.Dependency50.P47 (Law)

open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P39 (pushLaw)

open QAlgorithms.Papers.Independent.Support50.P16 (trivialMeasurement)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Appendix A, PDF p.12, and Appendix O, p.31: classical failure adds its
probability to P_luck. This is a common-experiment event comparison, with
agreement outside failure, rather than a composable protocol replacement. -/
theorem additive_classical_failure {Omega : Type} [Fintype Omega]
    (p : Law Omega) (badIdeal badActual failed : Omega → Prop)
    (hagrees : ∀ w, ¬ failed w → (badActual w ↔ badIdeal w))
    (luck failure : ℝ)
    (hluck : (∑ w, if badIdeal w then p.prob w else 0) ≤ luck)
    (hfailure : (∑ w, if failed w then p.prob w else 0) ≤ failure) :
    (∑ w, if badActual w then p.prob w else 0) ≤ luck + failure := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P77

end
