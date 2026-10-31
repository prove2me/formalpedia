-- Prove2me | Theorems.Thm_RegExperiment_proposition_6
-- name    : RegExperiment.proposition_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:46:22.915732+00:00
-- url     : https://prove2.me/theorems/5a2c47b3-4db4-4ca8-943b-6bb9167cc29a
-- title:
--   Proposition 6, p.21 — optimal mix of approval, withdrawal and liability: first best iff e ≤ ê, otherwise no liability and lenient standards (corrected: e ≤ ê, experimenting optima, interior prior)
-- statement:
--   Let $(s^*,S^*)$ be first-best standards (Proposition 1). There is a critical externality $\hat e\in(0,1)$, independent of the prior, such that for every externality rate $e\in[0,1]$ and every prior $\sigma_0\in(s^*,S^*)$:
--
--   1. **(a)(i)** the first best is achieved if and only if $e\le\hat e$; and if $e<\hat e$, every socially optimal mix $(S,z,L)$ of the three instruments uses a positive liability, $L>0$;
--   2. **(a)(ii)** if $e\ge\hat e$, every optimal mix under which the firm experiments ($s<\sigma_0<S$, with $s$ the firm's best reply) sets liability to zero, $L=0$;
--   3. **(b)** every optimal mix under which the firm experiments has standards equal to or more lenient than the socially optimal ones:
--   $$
--   S\le S^*,\qquad z\le z^*.
--   $$
--
--   Here the planner commits to an adoption standard $S$, a withdrawal standard $z$ and a liability $L\in[0,v_i-v^B_p]$, and the firm controls only its rejection standard. The result says that liability is used only to discourage excessive experimentation, and that whenever the regulator departs from the first-best standards it does so by being more lenient.
--
--   **Formalization Note** Optimal mixes are strong-Stackelberg optima; "all three instruments are used" is $L>0$ (the standards $S$, $z$ are committed in every mix).
--
--   Differences from the source:
--   - correction: first best achieved iff e < ê → iff e ≤ ê; reason: the paper's own Step 2 (p.42) and p.22 achieve the first best at e = ê with L = 0, and Step 3 excludes it for e > ê, so the set of such e is [0, ê] and no ê makes "iff e < ê" true
--   - correction: the conclusion for every optimal mix → for optimal mixes (S, z, L, s) under which the firm experiments, s < σ₀ < S; reason: for e near 1 and σ₀ ∈ (s*, z*) the optimal welfare is 0 and every mix under which the firm rejects at once is optimal, e.g. (S* + 1, z* + 1, L̄/2), violating L = 0, S ≤ S*, z ≤ z*
--   - correction: no restriction on the prior → priors σ₀ ∈ (s*, S*), with ê chosen before σ₀; reason: for σ₀ ≥ S* the mix (S = σ₀, z*, 0) makes the firm adopt at once, which is first best for every e < 1, contradicting "only if e ≤ ê"; the paper's analysis is for interior priors (p.37)
--   - reading: values of the stochastic experimentation/stopping problem over stopping rules → closed-form values of threshold policies (rejection s, adoption S, withdrawal z); reason: the paper's own model: fn.17 (p.10) defines (s*, S*) as the maximizer of u¹_p(σ₀, s, S) over thresholds; Lemmas 1–2 (the reduction to thresholds) are not formalized
--   - reading: r₁, r₂ use an undefined μ′₂ (p.33) and R₁, R₂ are not defined (fn.37) → λₙ = 2μₙ²/ρ², r₁,₂ = ½(1 ∓ √(1+4r/λ₂)), R₁,₂ = ½(1 ∓ √(1+4r/λ₁)); reason: derived from the dynamics of p.8 (log-odds drift ±λₙ, variance 2λₙ); reproduces the page's ψ, r₁ + r₂ = 1 and z*
--   - reading: "the first best is achieved" → some feasible mix and firm best reply attain the maximal welfare over all standards (s, S, z); reason: the paper means the policy (s*, z*, S*); under Proposition 1 the two coincide
--   - reading: "socially optimal mix" and "all three instruments are used" → a strong-Stackelberg optimum over (S, z, L) and the firm's best reply s; L > 0; reason: the paper presumes a unique best reply; S and z are committed in every mix of this regime, so "used" concerns L
--   - reading: research cost c, no sign stated (p.7) → c > 0; reason: fn.39, p.37 uses "research cost c > 0"; with c = 0 the planner never rejects and the standards of Proposition 1 do not exist
--   - encoding: discount rate r ≥ 0 (p.8) → r > 0; reason: every value divides by r (v/r, c/r); r = 0 is undefined, so only undefined cases are excluded
--   - generalization: v_i = (1−e)v^G_p > 0 (p.8), so e < 1 → e ∈ [0, 1], including e = 1; reason: footnote 33 (p.22) uses e = 1; the statement for e ∈ [0,1) is the source's claim
--   - encoding: beliefs and standards are probabilities q ∈ (0,1) → log-odds σ = log(q/(1−q)) ∈ ℝ; reason: the paper's own change of variables (1), p.8; a monotone bijection, so no instance changes
--   - encoding: the closed forms are written for z ≤ S and s < σ₀ < S only → immediate withdrawal (ψ = 1) for S < z, immediate rejection (value 0) for σ₀ ≤ s, immediate adoption (value u²(σ₀, z)) for S ≤ σ₀; reason: the stopping rules at the boundary; both closed forms are continuous there
--   - encoding: standards q ∈ [0,1], including the never-stop standards q = 0, 1 → finite log-odds standards s, S, z ∈ ℝ; reason: the never-stop policies are limits of finite standards, so they never beat the finite ones
--   - encoding: signal variance ρ² (p.8) → ρ > 0; reason: ρ = 0 makes λₙ undefined (division by zero); only undefined cases are excluded
-- source:
--   Henry–Loseto–Ottaviani, Regulation with Experimentation: Ex Ante Approval, Ex Post Withdrawal, and Liability, working paper (Nov. 2018), sha256 85244fd4…db793c, Proposition 6, p.21 (PDF p.22); proof pp.42–43

import Mathlib
import Definitions.Def_RegExperiment_Regulation

namespace RegExperiment

/-- **Proposition 6 (optimal mix of instruments), corrected.** Henry–Loseto–Ottaviani, working
paper (Nov. 2018), Proposition 6, p.21.

Let `(s*, S*)` be first-best standards (Proposition 1). There is a critical externality
`ê ∈ (0, 1)`, independent of the prior, such that for every externality `e ∈ [0, 1]` and every
prior `σ₀ ∈ (s*, S*)`:
* (a)(i) the first best is achieved if and only if `e ≤ ê`, and for `e < ê` every socially optimal
  mix uses a positive liability;
* (a)(ii) for `e ≥ ê`, every optimal mix under which the firm experiments sets liability to zero;
* (b) every optimal mix under which the firm experiments has adoption and withdrawal standards
  equal to or more lenient than `S*` and `z*`.

**Formalization Note** Corrections of the printed statement: "iff `e < ê`" → "iff `e ≤ ê`"
(the paper's own Step 2, p.42, achieves the first best at `e = ê`); (a)(ii) and (b) are for
optimal mixes under which the firm experiments (`s < σ₀ < S`); priors are in `(s*, S*)`. The
optimal mix is a strong-Stackelberg optimum over `(S, z, L)` and the firm's best reply `s`. -/
theorem proposition_6 (P : Params) (sS SS : ℝ) (hFB : IsFirstBest P sS SS) :
    ∃ ê : ℝ, 0 < ê ∧ ê < 1 ∧ ∀ e ∈ Set.Icc (0 : ℝ) 1, ∀ σ₀ ∈ Set.Ioo sS SS,
      (FirstBestAchieved P e σ₀ ↔ e ≤ ê) ∧
      (e < ê → ∀ S z L s : ℝ, IsOptimalMix P e σ₀ S z L s → 0 < L) ∧
      (ê ≤ e → ∀ S z L s : ℝ, IsOptimalMix P e σ₀ S z L s → s < σ₀ → σ₀ < S → L = 0) ∧
      (∀ S z L s : ℝ, IsOptimalMix P e σ₀ S z L s → s < σ₀ → σ₀ < S →
        S ≤ SS ∧ z ≤ zstar P) := by sorry

end RegExperiment
