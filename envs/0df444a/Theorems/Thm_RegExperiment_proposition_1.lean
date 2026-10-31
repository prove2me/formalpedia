-- Prove2me | Theorems.Thm_RegExperiment_proposition_1
-- name    : RegExperiment.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:46:14.790159+00:00
-- url     : https://prove2.me/theorems/e345936c-53eb-4f76-b7eb-126d623a5ed3
-- title:
--   Proposition 1, pp.8–9 — the planner's first best is given by standards $s^*\le z^*\le S^*$ independent of the belief
-- statement:
--   There are a rejection standard $s^*$ and an adoption standard $S^*$, not depending on the current belief, such that, with the withdrawal standard $z^*$:
--   1. $s^*\le z^*\le S^*$ (part (c));
--   2. for every prior $\sigma_0\in(s^*,S^*)$, experimenting between $s^*$ and $S^*$ and withdrawing at $z^*$ is optimal: $u^1_p(\sigma_0;s,S,z)\le u^1_p(\sigma_0;s^*,S^*,z^*)$ for all $(s,S,z)$ (parts (a)(ii) and (b));
--   3. for every prior $\sigma_0\le s^*$, no standards give positive welfare, $u^1_p(\sigma_0;s,S,z)\le 0$, so rejecting at once is optimal (part (a)(i));
--   4. for every prior $\sigma_0\ge S^*$, no standards beat adopting at once and withdrawing at $z^*$: $u^1_p(\sigma_0;s,S,z)\le u^2_p(\sigma_0,z^*)$ (parts (a)(iii) and (b)).
--
--   This is the planner benchmark against which every regulatory instrument of the paper is measured.
--
--   Differences from the source:
--   - reading: values of the stochastic experimentation/stopping problem over stopping rules → closed-form values of threshold policies (rejection s, adoption S, withdrawal z); reason: the paper's own model: fn.17 (p.10) defines (s*, S*) as the maximizer of u¹_p(σ₀, s, S) over thresholds; Lemmas 1–2 (the reduction to thresholds) are not formalized
--   - encoding: beliefs and standards are probabilities q ∈ (0,1) → log-odds σ = log(q/(1−q)) ∈ ℝ; reason: the paper's own change of variables (1), p.8; a monotone bijection, so no instance changes
--   - reading: r₁, r₂ use an undefined μ′₂ (p.33) and R₁, R₂ are not defined (fn.37) → λₙ = 2μₙ²/ρ², r₁,₂ = ½(1 ∓ √(1+4r/λ₂)), R₁,₂ = ½(1 ∓ √(1+4r/λ₁)); reason: derived from the dynamics of p.8 (log-odds drift ±λₙ, variance 2λₙ); reproduces the page's ψ, r₁ + r₂ = 1 and z*
--   - encoding: the closed forms are written for z ≤ S and s < σ₀ < S only → immediate withdrawal (ψ = 1) for S < z, immediate rejection (value 0) for σ₀ ≤ s, immediate adoption (value u²(σ₀, z)) for S ≤ σ₀; reason: the stopping rules at the boundary; both closed forms are continuous there
--   - encoding: standards q ∈ [0,1], including the never-stop standards q = 0, 1 → finite log-odds standards s, S, z ∈ ℝ; reason: the never-stop policies are limits of finite standards, so they never beat the finite ones
--   - encoding: discount rate r ≥ 0 (p.8) → r > 0; reason: every value divides by r (v/r, c/r); r = 0 is undefined, so only undefined cases are excluded
--   - reading: research cost c, no sign stated (p.7) → c > 0; reason: fn.39, p.37 uses "research cost c > 0"; with c = 0 the planner never rejects and the standards of Proposition 1 do not exist
--   - encoding: signal variance ρ² (p.8) → ρ > 0; reason: ρ = 0 makes λₙ undefined (division by zero); only undefined cases are excluded
--   - reading: "rejects if q ≤ s*", "adopts if q ≥ S*", "withdraws if q ≤ z*" → optimality of the corresponding values: welfare ≤ 0 below s*, ≤ u²_p(σ₀, z*) above S*, and (s*, S*, z*) optimal in between; reason: an optimal policy's action is the one whose value is maximal
-- source:
--   Henry–Loseto–Ottaviani, Regulation with Experimentation: Ex Ante Approval, Ex Post Withdrawal, and Liability, working paper (Nov. 2018), sha256 85244fd4…db793c, Proposition 1, pp.8–9 (PDF pp.9–10), with fn.17, p.10

import Mathlib
import Definitions.Def_RegExperiment_Regulation

namespace RegExperiment

/-- **Proposition 1 (the planner benchmark).** Henry–Loseto–Ottaviani, working paper (Nov. 2018),
Proposition 1, pp.8–9.

There are standards `s*` (rejection), `S*` (adoption), chosen independently of the current
belief, such that, with the withdrawal standard `z*`,
* `s* ≤ z* ≤ S*` (part (c));
* for every prior `σ₀ ∈ (s*, S*)` experimenting between `s*` and `S*` and withdrawing at `z*`
  is optimal among all standards (part (a)(ii) and (b));
* for every prior `σ₀ ≤ s*` no standards give positive welfare, so rejecting at once is optimal
  (part (a)(i));
* for every prior `σ₀ ≥ S*` no standards beat adopting at once and withdrawing at `z*`
  (part (a)(iii) and (b)).

**Formalization Note** Beliefs are log-odds. Policies are threshold policies valued by the
paper's closed forms (pp.10, 33–34); the paper's reduction to thresholds (Lemmas 1–2) is not
formalized. -/
theorem proposition_1 (P : Params) :
    ∃ sS SS : ℝ, sS ≤ zstar P ∧ zstar P ≤ SS ∧ IsFirstBest P sS SS ∧
      (∀ σ₀ : ℝ, σ₀ ≤ sS → ∀ s S z : ℝ, Wel P σ₀ s S z ≤ 0) ∧
      (∀ σ₀ : ℝ, SS ≤ σ₀ → ∀ s S z : ℝ, Wel P σ₀ s S z ≤ U2 P (P.vG, P.vB) σ₀ (zstar P)) := by sorry

end RegExperiment
