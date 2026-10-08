-- Prove2me | Theorems.Thm_ReedGGN_RenewalRep_corollary_5_2
-- name    : ReedGGN.RenewalRep.corollary_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:22:35.807916+00:00
-- url     : https://prove2.me/theorems/f7093352-48f6-403b-a67a-40bb3b224340
-- title:
--   Corollary 5.2 — (5.33) ⟺ (5.41) on càdlàg paths, and (5.41) has a unique càdlàg solution
-- statement:
--   Let $F$ be a service-time distribution: the distribution function of a probability measure $\mu$ on $[0,\infty)$ with mean $1$. Let $F_e$ be its equilibrium distribution (5.4) and $dM$ the renewal measure of the renewal process with interarrival law $F$. Fix a càdlàg driving path $\zeta$ on $[0,\infty)$ and $\beta\in\mathbb R$, and write $y^+=\max(y,0)$, $y^-=\min(y,0)$.
--
--   1. A càdlàg path $q$ solves the diffusion-limit equation
--   $$q(t)=\zeta(t)-\beta F_e(t)+\int_0^t q^+(t-s)\,dF(s),\qquad t\ge0,\tag{5.33}$$
--   if and only if it solves the renewal-function equation
--   $$q(t)=\zeta(t)+\int_0^t\zeta(t-u)\,dM(u)-\beta t-\int_0^t q^-(t-u)\,dM(u),\qquad t\ge0.\tag{5.41}$$
--   2. Equation (5.41) has a càdlàg solution, and any two càdlàg solutions agree on $[0,\infty)$.
--
--   In the paper this is the statement that the diffusion limit $\tilde Q_F$ of Theorem 5.1 "may be equivalently expressed as the unique strong solution" of (5.41), with $\zeta=\tilde\zeta=\tilde M_Q+\tilde Q_I$. For exponential service, $M(t)=t$ and (5.41) becomes the Halfin–Whitt diffusion.
--
--   **Formalization Note** The statement is pathwise: the paper's claim about the random process follows by applying it to each sample path $\tilde\zeta(\omega)$, which lies in $D[0,\infty)$ almost surely (p. 30); no probability space is built. "Unique strong solution" is made explicit as existence and uniqueness (on $[0,\infty)$) among càdlàg paths. The printed proof shows only that the solution of (5.33) satisfies (5.41); the converse and the uniqueness, which the paper asserts without writing out, are part of the statement, and the existence of a solution of (5.33) (Proposition 3.1 with $a=0$, $B=F$) is not assumed. All integrals are over the closed interval $[0,t]$.
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, p. 29, Corollary 5.2, Eq. (5.41); p. 25, Eq. (5.33)

import Mathlib
import Definitions.Def_ReedGGN_RenewalRep_Basic
import Definitions.Def_ReedGGN_RenewalRep_RenewalFunction
import Definitions.Def_ReedGGN_RenewalRep_Equations

namespace ReedGGN.RenewalRep

open MeasureTheory

/-- Corollary 5.2, p. 29, pathwise. For a service law `μ` (probability measure on `[0, ∞)` with
mean `1`), every càdlàg driving path `ζ` and every `β ∈ ℝ`:
1. a càdlàg path solves the limit equation (5.33) if and only if it solves the renewal-function
   equation (5.41);
2. (5.41) has a càdlàg solution, unique on `[0, ∞)` among càdlàg paths. -/
theorem corollary_5_2 (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ0 : μ (Set.Iio 0) = 0) (hint : Integrable id μ) (hmean : ∫ x, x ∂μ = 1)
    (ζ : ℝ → ℝ) (hζ : ReedGGN.Regulator.IsCadlag ζ) (β : ℝ) :
    (∀ q : ℝ → ℝ, ReedGGN.Regulator.IsCadlag q → (SolvesLimitEq μ ζ β q ↔ SolvesRenewalEq μ ζ β q)) ∧
    ∃ q : ℝ → ℝ, ReedGGN.Regulator.IsCadlag q ∧ SolvesRenewalEq μ ζ β q ∧
      ∀ q' : ℝ → ℝ, ReedGGN.Regulator.IsCadlag q' → SolvesRenewalEq μ ζ β q' → Set.EqOn q' q (Set.Ici 0) := by sorry

end ReedGGN.RenewalRep
