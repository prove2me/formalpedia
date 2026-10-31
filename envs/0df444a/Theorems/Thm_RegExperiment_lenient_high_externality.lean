-- Prove2me | Theorems.Thm_RegExperiment_lenient_high_externality
-- name    : RegExperiment.lenient_high_externality
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:46:31.172453+00:00
-- url     : https://prove2.me/theorems/692bf40c-d9c4-4057-9cea-af1ace2ed7f0
-- title:
--   Proof of Proposition 6, Step 3, p.43 — for $e>\hat e$ no liability and strictly more lenient $S<S^*$, $z<z^*$ (corrected: experimenting optima, interior prior)
-- statement:
--   Let $(s^*,S^*)$ be first-best standards and let $\hat e$ be the critical externality. For every $e\in(\hat e,1]$ and every prior $\sigma_0\in(s^*,S^*)$:
--   1. the first best is not achieved;
--   2. every optimal mix $(S,z,L)$ with a best reply $s$ of the firm under which the firm experiments ($s<\sigma_0<S$) has
--   $$
--   L=0,\qquad S<S^*,\qquad z<z^*.
--   $$
--   Above the critical externality the firm researches too little; liability would discourage research further, so the planner drops it and instead approves sooner and withdraws later.
--
--   Differences from the source:
--   - correction: the conclusion for every optimal mix → for optimal mixes (S, z, L, s) under which the firm experiments, s < σ₀ < S; reason: for e near 1 and σ₀ ∈ (s*, z*) the optimal welfare is 0 and every mix under which the firm rejects at once is optimal, e.g. (S* + 1, z* + 1, L̄/2), violating L = 0, S ≤ S*, z ≤ z*
--   - correction: no restriction on the prior → priors σ₀ ∈ (s*, S*); reason: for σ₀ ≥ S* the mix (S = σ₀, z*, 0) makes the firm adopt at once, which is first best for every e < 1; for σ₀ ≤ s* a large S makes the firm reject at once, which is first best
--   - encoding: ê of Step 1 → ê given by its defining property (IsCriticalExternality, the content of Step 1); reason: Step 1 shows that exactly one ê has this property
--   - reading: "socially optimal mix" (S_pp, z_pp, L_pp) with the firm's reply s_pp → a strong-Stackelberg optimum over (S, z, L) and the firm's best replies s; reason: the paper presumes a unique best reply; with several, the planner's choice among them is the standard reading
--   - generalization: v_i = (1−e)v^G_p > 0 (p.8), so e < 1 → e ∈ [0, 1], including e = 1; reason: footnote 33 (p.22) uses e = 1; the statement for e ∈ [0,1) is the source's claim
--   - reading: values of the stochastic experimentation/stopping problem over stopping rules → closed-form values of threshold policies (rejection s, adoption S, withdrawal z); reason: the paper's own model: fn.17 (p.10) defines (s*, S*) as the maximizer of u¹_p(σ₀, s, S) over thresholds; Lemmas 1–2 (the reduction to thresholds) are not formalized
--   - encoding: beliefs and standards are probabilities q ∈ (0,1) → log-odds σ = log(q/(1−q)) ∈ ℝ; reason: the paper's own change of variables (1), p.8; a monotone bijection, so no instance changes
--   - reading: r₁, r₂ use an undefined μ′₂ (p.33) and R₁, R₂ are not defined (fn.37) → λₙ = 2μₙ²/ρ², r₁,₂ = ½(1 ∓ √(1+4r/λ₂)), R₁,₂ = ½(1 ∓ √(1+4r/λ₁)); reason: derived from the dynamics of p.8 (log-odds drift ±λₙ, variance 2λₙ); reproduces the page's ψ, r₁ + r₂ = 1 and z*
--   - encoding: the closed forms are written for z ≤ S and s < σ₀ < S only → immediate withdrawal (ψ = 1) for S < z, immediate rejection (value 0) for σ₀ ≤ s, immediate adoption (value u²(σ₀, z)) for S ≤ σ₀; reason: the stopping rules at the boundary; both closed forms are continuous there
--   - encoding: standards q ∈ [0,1], including the never-stop standards q = 0, 1 → finite log-odds standards s, S, z ∈ ℝ; reason: the never-stop policies are limits of finite standards, so they never beat the finite ones
--   - encoding: discount rate r ≥ 0 (p.8) → r > 0; reason: every value divides by r (v/r, c/r); r = 0 is undefined, so only undefined cases are excluded
--   - reading: research cost c, no sign stated (p.7) → c > 0; reason: fn.39, p.37 uses "research cost c > 0"; with c = 0 the planner never rejects and the standards of Proposition 1 do not exist
--   - encoding: signal variance ρ² (p.8) → ρ > 0; reason: ρ = 0 makes λₙ undefined (division by zero); only undefined cases are excluded
-- source:
--   Henry–Loseto–Ottaviani, Regulation with Experimentation: Ex Ante Approval, Ex Post Withdrawal, and Liability, working paper (Nov. 2018), sha256 85244fd4…db793c, Proof of Proposition 6, Step 3, p.43 (PDF p.44), and p.22 ("the first best is no longer achievable")

import Mathlib
import Definitions.Def_RegExperiment_Regulation

namespace RegExperiment

/-- **No liability and lenient standards for `e > ê`.** Henry–Loseto–Ottaviani, working paper
(Nov. 2018), Proof of Proposition 6, Step 3, p.43 (and p.22: "if `e > ê`, the first best is no
longer achievable").

Let `(s*, S*)` be first-best standards and `ê` the critical externality. For every
`e ∈ (ê, 1]` and every prior `σ₀ ∈ (s*, S*)`: the first best is not achieved, and every optimal
mix `(S, z, L)` with a best reply `s` under which the firm experiments (`s < σ₀ < S`) has `L = 0`,
`S < S*` and `z < z*`.

**Formalization Note** Corrected: the conclusion is for optimal mixes under which the firm
experiments, and for priors in `(s*, S*)`. -/
theorem lenient_high_externality (P : Params) (sS SS ê : ℝ) (hFB : IsFirstBest P sS SS)
    (hê : IsCriticalExternality P sS SS ê) :
    ∀ e ∈ Set.Ioc ê 1, ∀ σ₀ ∈ Set.Ioo sS SS,
      ¬ FirstBestAchieved P e σ₀ ∧
        ∀ S z L s : ℝ, IsOptimalMix P e σ₀ S z L s → s < σ₀ → σ₀ < S →
          L = 0 ∧ S < SS ∧ z < zstar P := by sorry

end RegExperiment
