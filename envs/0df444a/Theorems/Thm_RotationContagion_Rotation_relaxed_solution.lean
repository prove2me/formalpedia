-- Prove2me | Theorems.Thm_RotationContagion_Rotation_relaxed_solution
-- name    : RotationContagion.Rotation.relaxed_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:21:32.300275+00:00
-- url     : https://prove2.me/theorems/c67e4575-3242-490e-a212-87721f89c434
-- title:
--   Proof of Proposition 1, pp. 10–11 — solution of the relaxed problem (P2)
-- statement:
--   Assume $\gamma > 0$, $K > 1$, $R \ge 0$, and let $f(\tau) = \ell(\tau) + \ell(R-\tau)$. The relaxed rotation problem (P2) is
--   $$\min_F\ \mathrm E_F\big[\ell(\tau) + \ell(R-\tau)\big] \quad\text{s.t.}\quad \mathrm E_F\,\tau = \frac R2,$$
--   over probability distributions $F$ of the exposure time on $[0,R]$.
--
--   1. If $R/2 < b$, the point mass $\delta_{R/2}$ is feasible (its mean is $R/2$) and optimal: $\int f\,d\delta_{R/2} \le \int f\,d\nu$ for every probability measure $\nu$ on $[0,R]$ with mean $R/2$.
--   2. If $R/2 > b$, the distribution $\nu_0 = \tfrac12\delta_0 + \tfrac12\delta_R$ is feasible (its mean is $R/2$) and optimal: $\int f\,d\nu_0 \le \int f\,d\nu$ for every probability measure $\nu$ on $[0,R]$ with mean $R/2$.
--
--   These are the two candidate solutions that Proposition 1 then implements by rotation schedules.
--
--   **Formalization Note** "Distribution on $[0,R]$" is the hypothesis $\nu(\mathbb R \setminus [0,R]) = 0$; exposure times lie in $[0,R]$. The page's constraint $\mathrm E_F\tau = R/2$ is kept as a hypothesis.
-- source:
--   Ely, Galeotti & Steiner, Rotation as Contagion Mitigation, working paper of 29 October 2020 (published Management Science 2021, doi:10.1287/mnsc.2020.3910), pp. 10–11, proof of Proposition 1; (P2) on p. 8

import Mathlib
import Definitions.Def_RotationContagion_Rotation_Model

namespace RotationContagion.Rotation

open MeasureTheory

/-- Proof of Proposition 1, pp. 10–11: solution of the relaxed problem (P2),
`min_F E_F[ℓ(τ) + ℓ(R - τ)]` subject to `E_F τ = R/2`, over laws `ν` of `τ` on `[0, R]`.
If `R/2 < b`, the point mass at `R/2` is feasible and optimal; if `R/2 > b`, the law putting
probability one half on each of `0` and `R` is feasible and optimal. -/
theorem relaxed_solution (P : Params) (hP : P.Standing) :
    (P.R / 2 < b P →
      ∫ x, x ∂(Measure.dirac (P.R / 2)) = P.R / 2 ∧
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ν (Set.Icc 0 P.R)ᶜ = 0 →
        ∫ x, x ∂ν = P.R / 2 →
          ∫ τ, relaxedObj P τ ∂(Measure.dirac (P.R / 2)) ≤ ∫ τ, relaxedObj P τ ∂ν) ∧
    (b P < P.R / 2 →
      ∫ x, x ∂((1 / 2 : ENNReal) • Measure.dirac 0 + (1 / 2 : ENNReal) • Measure.dirac P.R) =
          P.R / 2 ∧
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ν (Set.Icc 0 P.R)ᶜ = 0 →
        ∫ x, x ∂ν = P.R / 2 →
          ∫ τ, relaxedObj P τ
              ∂((1 / 2 : ENNReal) • Measure.dirac 0 + (1 / 2 : ENNReal) • Measure.dirac P.R) ≤
            ∫ τ, relaxedObj P τ ∂ν) := by sorry

end RotationContagion.Rotation
