-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P73_memoryless_wiretap_exponents
-- name    : QAlgorithms.Papers.Independent.Intake100.P73.memoryless_wiretap_exponents
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:57:54.029+00:00
-- url     : https://prove2.me/theorems/818aa7ac-51c5-48a8-9d23-c5af25b679a9
-- title:
--   Theorem 7: simultaneous memoryless wiretap exponents
-- statement:
--   Let $B:X\to\mathcal P(Y)$ and $E:X\to\mathcal P(Z)$ be classical discrete memoryless channels, with $Z$ finite, a common normalized input law $p$, and message and randomization rates $R,R'\ge0$. No degradedness, finite-input, or mutual-information rate separation is assumed. Use natural logarithms and full L1. For $V=B,E$, define $V_p=\sum_xp(x)V_x$, $\phi(t\mid V,p)=\log\sum_y(\sum_xp(x)V_x(y)^{1/(1+t)})^{1+t}$, and $\psi(s\mid V,p)=\log\sum_y(\sum_xp(x)V_x(y)^{1+s})V_p(y)^{-s}$, excluding zero-mixture terms; both zero-parameter endpoints have value zero.
--
--   There exists ONE sequence $\Phi_n$ of stochastic wiretap codes for $B^n,E^n$, with disjoint Bob decoding regions and uniform messages, such that
--   $$
--   \lim_n\frac{\log|\Phi_n|}{n}=R,
--   $$
--   $$
--   \liminf_n-\frac1n\log\epsilon_B(\Phi_n)\ge
--   \sup_{0\le s\le1}\{-\phi(s\mid B,p)-s(R+R')\},
--   $$
--   $$
--   \liminf_n-\frac1n\log I_E(\Phi_n)\ge
--   \sup_{-1/2\le t\le0}\{-\phi(t\mid E,p)-tR'\},
--   $$
--   $$
--   \liminf_n-\frac1n\log d_E(\Phi_n)\ge
--   \sup_{0\le s\le1}\frac{-\psi(s\mid E,p)+sR'}{1+s},
--   $$
--   $$
--   \liminf_n-\frac1n\log d_E(\Phi_n)\ge
--   \tfrac12\sup_{-1/2\le t\le0}\{-\phi(t\mid E,p)-tR'\}.
--   $$
--   Here $\epsilon_B$ is average Bob error, $I_E$ is the average KL of each message's Eve output against their uniform mixture, and $d_E$ is full L1 averaged over ordered distinct message pairs, set to zero for one message. Exact zero error or leakage gives exponent $+\infty$. These are simultaneous reliability and secrecy guarantees, including the zero-rate endpoints.
--
--   **Formalization Note.** The source prints “any real numbers” for both rates. The domain is corrected to nonnegative rates, as forced by positive integer message and randomization counts in its proof. Negative message rates cannot be attained; negative randomization rates can make the reliability claim false on a constant Bob channel. This paper's pairwise $d_E$ is distinct from the later paper's message–Eve distance.
-- source:
--   General non-asymptotic and asymptotic formulas in channel resolvability and identification capacity and their application to wire-tap channel, arXiv:cs/0503088v2, PDF p. 12, Theorem 7, (58)–(61): simultaneous memoryless wiretap exponents

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P73

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P73

open Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

universe u

/-- Hayashi, PDF p.12, Theorem 7, (58)–(61): ONE sequence attains the rate and
ALL FOUR exponent bounds. SOURCE DOMAIN CORRECTION: printed 'any real numbers
R,Rprime' is restricted to R,Rprime>=0, as forced by positive message and
randomization counts in the proof. Leakage is the source's PAIRWISE full L1,
not the later paper's message–Eve distance. Zero errors have +infinity exponents.
The proof cites (21) for the hayashiPhi bound, evidently meaning (22).
Printed (61) uses a plain lim; changed to liminf, as the preceding Pinsker
comparison applied to (59) controls the lower exponent without asserting convergence. -/
theorem memoryless_wiretap_exponents {X Y Z : Type*} [Finite Z]
    (B : X → Y → ℝ≥0∞) (E : X → Z → ℝ≥0∞)
    (hB : IsDiscreteStochastic B) (hE : IsDiscreteStochastic E) (p : PMF X)
    (R Rprime : ℝ) (hR : 0 ≤ R) (hRp : 0 ≤ Rprime) :
    ∃ c : (k : ℕ) → DiscreteStochasticWiretapCode (Fin (length k) → X) (Fin (length k) → Y),
      Tendsto (fun k => Real.log (c k).messages / (length k : ℝ)) atTop (nhds R) ∧
      reliabilityExponent B p (R + Rprime) ≤
        liminfErrorExponent (fun k => averageBobError (memorylessKernel B (length k)) (c k)) ∧
      phiExponent E p Rprime ≤
        liminfErrorExponent (fun k => averageEveDivergence (memorylessKernel E (length k)) (c k)) ∧
      psiExponent E p Rprime ≤
        liminfErrorExponent (fun k => eveDistance (memorylessKernel E (length k)) (c k)) ∧
      phiExponent E p Rprime / 2 ≤
        liminfErrorExponent (fun k => eveDistance (memorylessKernel E (length k)) (c k)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P73

end
