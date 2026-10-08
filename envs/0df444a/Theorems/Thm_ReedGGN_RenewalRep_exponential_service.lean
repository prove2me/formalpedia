-- Prove2me | Theorems.Thm_ReedGGN_RenewalRep_exponential_service
-- name    : ReedGGN.RenewalRep.exponential_service
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:23:16.522404+00:00
-- url     : https://prove2.me/theorems/c9d97788-e47e-4126-8bef-3683d8126172
-- title:
--   p. 31, (5.46) — exponential service: M(t) = t, and (5.41) becomes q = ζ + ∫ζ − βt − ∫q⁻
-- statement:
--   Let $F$ be the exponential distribution of rate $1$ (mean $1$), with renewal measure $dM$.
--
--   1. The renewal function is the identity: $M(t)=dM((-\infty,t])=t$ for every $t\ge0$ (the renewal process is a rate-$1$ Poisson process).
--   2. Consequently, for càdlàg paths $\zeta$, $q$ and $\beta\in\mathbb R$, $q$ solves (5.41) if and only if
--   $$q(t)=\zeta(t)+\int_0^t\zeta(s)\,ds-\beta t-\int_0^t q^-(s)\,ds,\qquad t\ge0,\tag{5.46}$$
--   with $q^-=\min(q,0)$.
--
--   This is the form in which Corollary 5.2 recovers the Halfin–Whitt diffusion limit for the $GI/M/N$ queue.
--
--   **Formalization Note** Part 1 is stated as an identity of extended nonnegative reals, so it includes finiteness. The paper's subsequent claim that $\tilde\zeta(t)+\int_0^t\tilde\zeta(s)\,ds$ is a Brownian motion ("extensive covariance calculations") is not formalized. The integrals in (5.46) are Lebesgue integrals over $[0,t]$.
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, p. 31, Eq. (5.46)

import Mathlib
import Definitions.Def_ReedGGN_RenewalRep_Basic
import Definitions.Def_ReedGGN_RenewalRep_RenewalFunction
import Definitions.Def_ReedGGN_RenewalRep_Equations

namespace ReedGGN.RenewalRep

open MeasureTheory ProbabilityTheory

/-- p. 31, (5.46): for exponential service times of rate `1` (mean `1`),
(a) the renewal function is `M(t) = t` for `t ≥ 0`, as an identity of extended reals;
(b) for càdlàg `ζ` and `q` and `β ∈ ℝ`, (5.41) is equivalent to (5.46):
`q(t) = ζ(t) + ∫_0^t ζ(s) ds − β t − ∫_0^t q⁻(s) ds` for every `t ≥ 0`, `q⁻ = min(q, 0)`. -/
theorem exponential_service :
    (∀ t : ℝ, 0 ≤ t → renewalMeasure (expMeasure 1) (Set.Iic t) = ENNReal.ofReal t) ∧
    (∀ (ζ : ℝ → ℝ) (β : ℝ) (q : ℝ → ℝ), ReedGGN.Regulator.IsCadlag ζ → ReedGGN.Regulator.IsCadlag q →
      (SolvesRenewalEq (expMeasure 1) ζ β q ↔
        ∀ t : ℝ, 0 ≤ t →
          q t = ζ t + (∫ s in Set.Icc 0 t, ζ s) - β * t - ∫ s in Set.Icc 0 t, min (q s) 0)) := by sorry

end ReedGGN.RenewalRep
