-- Prove2me | Theorems.Thm_RegExperiment_optimal_withdrawal_standard
-- name    : RegExperiment.optimal_withdrawal_standard
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:44:34.867347+00:00
-- url     : https://prove2.me/theorems/9dfc05c3-45f5-4478-8bfb-1ae9d61df555
-- title:
--   Proof of Proposition 1, Step 1, p.33 — the withdrawal standard $z^*$ maximizes the ex post value for every adoption belief
-- statement:
--   Let $r_1=\frac12(1-\sqrt{1+4r/\lambda_2})$ and $r_2=\frac12(1+\sqrt{1+4r/\lambda_2})$. Then
--   $$
--   r_1<0<r_2,\qquad r_1<r_2,\qquad r_1+r_2=1,
--   $$
--   and for every adoption belief $S$ and every withdrawal standard $z$ the planner's ex post value satisfies
--   $$
--   u^2_p(S,z)\le u^2_p(S,z^*),\qquad z^*=-\ln\frac{v^G_p\,r_2}{v^B_p\,r_1}.
--   $$
--   So the optimal withdrawal standard $z^*$ does not depend on the belief $S$ at which the product was adopted.
--
--   This is the ex post (bandit) half of the planner's benchmark: it fixes the payoff upon adoption that the ex ante Wald problem takes as given.
--
--   Differences from the source:
--   - encoding: beliefs and standards are probabilities q ∈ (0,1) → log-odds σ = log(q/(1−q)) ∈ ℝ; reason: the paper's own change of variables (1), p.8; a monotone bijection, so no instance changes
--   - reading: r₁, r₂ use an undefined μ′₂ (p.33) and R₁, R₂ are not defined (fn.37) → λₙ = 2μₙ²/ρ², r₁,₂ = ½(1 ∓ √(1+4r/λ₂)), R₁,₂ = ½(1 ∓ √(1+4r/λ₁)); reason: derived from the dynamics of p.8 (log-odds drift ±λₙ, variance 2λₙ); reproduces the page's ψ, r₁ + r₂ = 1 and z*
--   - encoding: the closed forms are written for z ≤ S and s < σ₀ < S only → immediate withdrawal (ψ = 1) for S < z, immediate rejection (value 0) for σ₀ ≤ s, immediate adoption (value u²(σ₀, z)) for S ≤ σ₀; reason: the stopping rules at the boundary; both closed forms are continuous there
--   - encoding: discount rate r ≥ 0 (p.8) → r > 0; reason: every value divides by r (v/r, c/r); r = 0 is undefined, so only undefined cases are excluded
--   - encoding: signal variance ρ² (p.8) → ρ > 0; reason: ρ = 0 makes λₙ undefined (division by zero); only undefined cases are excluded
--   - encoding: research cost c (no sign stated) → c > 0, carried by the parameter structure; reason: c does not enter this statement; the structure holds the model's standing assumptions
-- source:
--   Henry–Loseto–Ottaviani, Regulation with Experimentation: Ex Ante Approval, Ex Post Withdrawal, and Liability, working paper (Nov. 2018), sha256 85244fd4…db793c, Proof of Proposition 1, Step 1, p.33 (PDF p.34)

import Mathlib
import Definitions.Def_RegExperiment_Model

namespace RegExperiment

/-- **Optimal withdrawal standard.** Henry–Loseto–Ottaviani, working paper (Nov. 2018),
Proof of Proposition 1, Step 1, p.33.

The ex post exponents satisfy `r₁ < 0 < r₂`, `r₁ < r₂` and `r₁ + r₂ = 1`, and for every adoption
belief `S` the withdrawal standard `z* = −ln(v^G_p r₂/(v^B_p r₁))` maximizes the planner's ex post
value `u²_p(S, z)` over all withdrawal standards `z`; in particular `z*` does not depend on `S`.

**Formalization Note** Beliefs are log-odds. The page maximizes over `z ≤ S`; a standard `z > S`
means immediate withdrawal (value `0`), which is part of the model (`psiPost`). -/
theorem optimal_withdrawal_standard (P : Params) :
    r1 P < 0 ∧ 0 < r2 P ∧ r1 P < r2 P ∧ r1 P + r2 P = 1 ∧
      ∀ S z : ℝ, U2 P (P.vG, P.vB) S z ≤ U2 P (P.vG, P.vB) S (zstar P) := by sorry

end RegExperiment
