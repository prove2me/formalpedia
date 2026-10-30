-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P31_power_law_density_moments
-- name    : QAlgorithms.Papers.Independent.Advance50.P31.power_law_density_moments
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T13:12:40.372248+00:00
-- url     : https://prove2.me/theorems/03c9b89b-bb8d-4379-a168-b9a7c98aca61
-- title:
--   Continuum power-law density and Boltzmann moment ratios
-- statement:
--   Let $A,a,\beta>0$ and let $\rho(\epsilon)=A\epsilon^{a-1}$ on $\epsilon>0$. For a power-law trap $V(x)=|x|^\gamma$ in dimension $d$, the exponent is $a=d/\gamma+d/2$; $A$ is the shared positive phase-space normalization. For every positive integer $k$, define continuum moments
--
--   $$
--   S_k=\int_0^\infty\rho(\epsilon)e^{-k\beta\epsilon}\,d\epsilon,
--   \qquad
--   D_k=\int_0^\infty\beta\epsilon\,\rho(\epsilon)e^{-k\beta\epsilon}\,d\epsilon.
--   $$
--
--   Both integrands are integrable and
--
--   $$
--   S_k=\frac{A\Gamma(a)}{(k\beta)^a},\qquad
--   \frac{D_k}{S_k}=\frac{a}{k}.
--   $$
--
--   In particular, $D_1/S_1=a$ and $D_2/S_2=a/2$. If $a>1$, the correctly normalized quadratic Bose coefficient satisfies
--
--   $$
--   \alpha_2^b=\frac{S_2(1-a)}{2}<0.
--   $$
--
--   These are continuum moment identities and do not replace an arbitrary trap's discrete counting measure by an equal continuum density. **Source corrections:** Eq.(87)'s intermediate Gamma quotient has shifted indices; it must be $\Gamma(a+1)/\Gamma(a)$. Eqs.(91),(92) have an erroneous negative energy exponent; Eq.(86) fixes the intended exponent $a-1$. Definition (77) already includes the factor $\beta$, so no additional $\beta$ belongs in the moment ratio.
-- source:
--   Capacities of noiseless quantum channels for massive indistinguishable particles: Bosons vs. fermions, arXiv:quant-ph/0512200v3, PDF p. 14, §IX, Eqs.(86)–(88)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P31

noncomputable section

open MeasureTheory

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Advance50.P31

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass operatorTrace)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {I : Type*} [Countable I]

/-- PDF p.14, Eqs.(86)--(88): continuum Boltzmann moments and their ratios.
SOURCE CORRECTIONS: the intermediate Gamma quotient in (87) is
Gamma(a+1)/Gamma(a), and the exponents in (91),(92) are positive a-1 as in (86).
D_k already includes beta in Eq.(77); there is no extra beta in the ratio or alpha.
Only the final sign requires a>1; the moment identities need a>0. -/
theorem power_law_density_moments
    (A a beta : ℝ) (hA : 0 < A) (ha : 0 < a) (hbeta : 0 < beta) :
    (∀ k : ℕ, 0 < k →
      IntegrableOn (fun e => densityOfStates A a e *
        Real.exp (-(k : ℝ) * beta * e)) (Set.Ioi (0 : ℝ)) ∧
      IntegrableOn (fun e => beta * e * densityOfStates A a e *
        Real.exp (-(k : ℝ) * beta * e)) (Set.Ioi (0 : ℝ)) ∧
      boltzmannMoment A a beta k = A * Real.Gamma a / ((k : ℝ) * beta) ^ a ∧
      weightedMoment A a beta k / boltzmannMoment A a beta k = a / (k : ℝ)) ∧
    (1 < a → boltzmannMoment A a beta 2 * (1 - a) / 2 < 0) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P31

end
