-- Prove2me | Theorems.Thm_RegExperiment_expost_value_shape
-- name    : RegExperiment.expost_value_shape
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:44:53.904455+00:00
-- url     : https://prove2.me/theorems/3aa202ee-1fbe-4d2c-ae83-b967475f2b66
-- title:
--   Proof of Proposition 1, Step 3, p.35 — $\hat u^2_p$ vanishes up to $z^*$, then is positive and strictly increasing
-- statement:
--   Let $\hat u^2_p(\sigma)=u^2_p(\sigma,z^*)$ be the planner's ex post value after adoption at belief $\sigma$ with withdrawal at $z^*$. Then
--   1. $\hat u^2_p(\sigma)=0$ for every $\sigma\le z^*$;
--   2. $\hat u^2_p(\sigma)>0$ for every $\sigma>z^*$;
--   3. $\hat u^2_p$ is strictly increasing on $(z^*,\infty)$.
--
--   In particular $\hat u^2_p\ge 0$ everywhere. This is the fact behind the ordering $s^*\le z^*\le S^*$ of Proposition 1.
--
--   Differences from the source:
--   - encoding: beliefs and standards are probabilities q ∈ (0,1) → log-odds σ = log(q/(1−q)) ∈ ℝ; reason: the paper's own change of variables (1), p.8; a monotone bijection, so no instance changes
--   - reading: r₁, r₂ use an undefined μ′₂ (p.33) and R₁, R₂ are not defined (fn.37) → λₙ = 2μₙ²/ρ², r₁,₂ = ½(1 ∓ √(1+4r/λ₂)), R₁,₂ = ½(1 ∓ √(1+4r/λ₁)); reason: derived from the dynamics of p.8 (log-odds drift ±λₙ, variance 2λₙ); reproduces the page's ψ, r₁ + r₂ = 1 and z*
--   - encoding: the closed forms are written for z ≤ S and s < σ₀ < S only → immediate withdrawal (ψ = 1) for S < z, immediate rejection (value 0) for σ₀ ≤ s, immediate adoption (value u²(σ₀, z)) for S ≤ σ₀; reason: the stopping rules at the boundary; both closed forms are continuous there
--   - encoding: discount rate r ≥ 0 (p.8) → r > 0; reason: every value divides by r (v/r, c/r); r = 0 is undefined, so only undefined cases are excluded
--   - encoding: signal variance ρ² (p.8) → ρ > 0; reason: ρ = 0 makes λₙ undefined (division by zero); only undefined cases are excluded
--   - encoding: research cost c (no sign stated) → c > 0, carried by the parameter structure; reason: c does not enter this statement; the structure holds the model's standing assumptions
-- source:
--   Henry–Loseto–Ottaviani, Regulation with Experimentation: Ex Ante Approval, Ex Post Withdrawal, and Liability, working paper (Nov. 2018), sha256 85244fd4…db793c, Proof of Proposition 1, Step 3, p.35 (PDF p.36)

import Mathlib
import Definitions.Def_RegExperiment_Model

namespace RegExperiment

/-- **Shape of the planner's ex post value.** Henry–Loseto–Ottaviani, working paper (Nov. 2018),
Proof of Proposition 1, Step 3, p.35.

Let `û²_p(σ) = u²_p(σ, z*)` be the planner's ex post value after adoption at belief `σ` with
withdrawal at `z*`. Then `û²_p(σ) = 0` for all `σ ≤ z*`, and `û²_p` is positive and strictly
increasing on `σ > z*`.

**Formalization Note** Beliefs are log-odds; `û²_p` is `U2 P (P.vG, P.vB) · (zstar P)`. -/
theorem expost_value_shape (P : Params) :
    (∀ σ : ℝ, σ ≤ zstar P → U2 P (P.vG, P.vB) σ (zstar P) = 0) ∧
      (∀ σ : ℝ, zstar P < σ → 0 < U2 P (P.vG, P.vB) σ (zstar P)) ∧
      StrictMonoOn (fun σ : ℝ => U2 P (P.vG, P.vB) σ (zstar P)) (Set.Ioi (zstar P)) := by sorry

end RegExperiment
