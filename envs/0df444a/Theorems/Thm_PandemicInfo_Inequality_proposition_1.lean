-- Prove2me | Theorems.Thm_PandemicInfo_Inequality_proposition_1
-- name    : PandemicInfo.Inequality.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:34:00.540173+00:00
-- url     : https://prove2.me/theorems/b927952b-c92d-47e4-b798-18027e3e04a0
-- title:
--   Proposition 1, p. 8 (PDF 9) — unique threshold BNE $c^\star(\mu)$, $P_{a^\star,\mu}=c^\star(\mu)/(\mu\kappa)$, $c^\star$ increasing concave
-- statement:
--   **Proposition 1 (equilibrium characterization).** Fix the model of §2 and a perceived infectiousness $\mu\in[\omega_\ell,\omega_h]$. Let
--
--   $$c^\star(\mu)=\frac{\mu\kappa(\theta+\sigma\sqrt3)}{\sigma2\sqrt3+\mu\kappa}.$$
--
--   1. The threshold profile $a^\star(c,\mu)=1$ for $c\le c^\star(\mu)$ and $a^\star(c,\mu)=0$ otherwise is a Bayesian Nash equilibrium at every $\mu\in[\omega_\ell,\omega_h]$.
--   2. Every BNE profile $a$ at $\mu$ isolates every type $c\in\mathcal C$ with $c<c^\star(\mu)$, lets every type $c\in\mathcal C$ with $c>c^\star(\mu)$ interact, and has active population
--   $$P_{a,\mu}=\frac{c^\star(\mu)}{\mu\kappa}.$$
--   3. On $[\omega_\ell,\omega_h]$ the threshold $c^\star$ is strictly increasing and concave, and $\mu\mapsto c^\star(\mu)/(\mu\kappa)$ is strictly decreasing.
--
--   The proposition reduces the government's problem to a problem in the threshold $c^\star(\mu_m)$ of each posterior.
--
--   **Formalization Note** The paper's "unique" BNE is unique up to the indifferent type $c=c^\star(\mu)$, where (7) allows both actions; the Lean states uniqueness for $c\ne c^\star(\mu)$ and the uniqueness of the active population. "Increases concavely" is strict monotonicity plus concavity; "decreases" is strict. All statements assume the standing assumptions of §2 (`Params.Standing`).
-- source:
--   de Véricourt, Gurkan, Wang, Informing the Public about a Pandemic, ESMT Working Paper 20-03 (Dec. 15, 2020), p. 8 (PDF 9), Proposition 1, (7)–(8); p. 16 (PDF 17), closed form of c⋆(µ)

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_PandemicInfo_Inequality_Model
import Definitions.Def_PandemicInfo_Inequality_Reduced

namespace PandemicInfo.Inequality

/-- Proposition 1, p. 8: the threshold profile (7) is a BNE; at every `µ ∈ [ω_ℓ, ω_h]` every BNE
isolates the types below `c⋆(µ)`, lets the types above `c⋆(µ)` interact, and has active population
(8) `c⋆(µ)/(µκ)`; `c⋆` is strictly increasing and concave and `c⋆(µ)/(µκ)` strictly decreasing. -/
theorem proposition_1 (P : Params) (hS : P.Standing) :
    P.IsBNEProfile (fun c μ => if c ≤ P.cStar μ then 1 else 0) ∧
    (∀ μ ∈ Set.Icc P.ωl P.ωh, ∀ a : ℝ → ℝ → ℝ, P.IsBNEAt a μ →
      (∀ c ∈ Set.Icc P.cLo P.cHi, c < P.cStar μ → a c μ = 1) ∧
      (∀ c ∈ Set.Icc P.cLo P.cHi, P.cStar μ < c → a c μ = 0) ∧
      P.activePop a μ = P.cStar μ / (μ * P.κ)) ∧
    StrictMonoOn P.cStar (Set.Icc P.ωl P.ωh) ∧
    ConcaveOn ℝ (Set.Icc P.ωl P.ωh) P.cStar ∧
    StrictAntiOn (fun μ => P.cStar μ / (μ * P.κ)) (Set.Icc P.ωl P.ωh) := by sorry

end PandemicInfo.Inequality
