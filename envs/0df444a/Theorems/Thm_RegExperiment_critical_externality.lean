-- Prove2me | Theorems.Thm_RegExperiment_critical_externality
-- name    : RegExperiment.critical_externality
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:46:22.475998+00:00
-- url     : https://prove2.me/theorems/4d1a8d9e-e74e-4cee-b07f-bdd0e5d3d3a3
-- title:
--   Proof of Proposition 6, Step 1, p.42 — a unique critical externality $\hat e\in(0,1)$ at which $(S^*,z^*)$ alone yields the first best (corrected: interior prior)
-- statement:
--   Let $(s^*,S^*)$ be first-best standards with $s^*<S^*$. There is a unique $\hat e$ such that
--   1. $\hat e\in(0,1)$;
--   2. for every prior $\sigma_0\in(s^*,S^*)$ and every $e\in[0,1]$, when the planner commits to $S=S^*$, $z=z^*$ and no liability, every best reply $s$ of the firm satisfies $s<s^*$ if $e<\hat e$ (excessive research) and $s>s^*$ if $e>\hat e$ (insufficient research);
--   3. at $e=\hat e$, for every prior $\sigma_0$, the first-best rejection standard $s^*$ is a best reply of the firm to $(S^*,z^*,L=0)$, so committing to the socially optimal adoption and withdrawal standards achieves the socially optimal policy $(s^*,z^*,S^*)$.
--
--   The critical externality $\hat e$ does not depend on the prior; it is the threshold of Proposition 6.
--
--   Differences from the source:
--   - reading: "If e → 1 … s_pp → S* > s*" and "By continuity there exists ê" → the sign pattern s_pp > s* for e ∈ (ê, 1] and ê ∈ (0, 1); reason: the limit is a step of the existence argument; near e = 1 the firm rejects at once at an interior prior, so the limit of a best reply is not determined, while the sign pattern is what Steps 2–3 use
--   - correction: the firm's reply s_pp compared with s*, no restriction on the prior → the sign pattern (s_pp < s* below ê, > s* above) for priors σ₀ ∈ (s*, S*); reason: for σ₀ ≥ S* the firm adopts at once and every s < σ₀ is a best reply, including s > s* when e < ê; the paper's analysis is for interior priors (p.37: "Focusing on q₀ ∈ (s*, S*)")
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
--   Henry–Loseto–Ottaviani, Regulation with Experimentation: Ex Ante Approval, Ex Post Withdrawal, and Liability, working paper (Nov. 2018), sha256 85244fd4…db793c, Proof of Proposition 6, Step 1, p.42 (PDF p.43)

import Mathlib
import Definitions.Def_RegExperiment_Regulation

namespace RegExperiment

/-- **The critical externality.** Henry–Loseto–Ottaviani, working paper (Nov. 2018), Proof of
Proposition 6, Step 1, p.42.

Let `(s*, S*)` be first-best standards with `s* < S*`. There is a unique `ê` such that
`ê ∈ (0, 1)`; for every prior `σ₀ ∈ (s*, S*)` and every `e ∈ [0, 1]`, when the planner commits to
`S = S*`, `z = z*` and no liability, every best reply of the firm lies below `s*` if `e < ê` and
above `s*` if `e > ê`; and at `e = ê` the first-best rejection standard `s*` is a best reply of
the firm for every prior `σ₀`, so the socially optimal policy is achieved.

**Formalization Note** `ê` is chosen before the prior. The page's limit "`e → 1` … `s_pp → S*`"
is replaced by the sign pattern above `ê`. The sign pattern is for priors in `(s*, S*)`. -/
theorem critical_externality (P : Params) (sS SS : ℝ) (hFB : IsFirstBest P sS SS)
    (hlt : sS < SS) :
    ∃! ê : ℝ, IsCriticalExternality P sS SS ê ∧
      ∀ σ₀ : ℝ, FirmBR P ê σ₀ SS (zstar P) 0 sS := by sorry

end RegExperiment
