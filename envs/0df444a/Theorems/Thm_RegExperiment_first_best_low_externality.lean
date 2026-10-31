-- Prove2me | Theorems.Thm_RegExperiment_first_best_low_externality
-- name    : RegExperiment.first_best_low_externality
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:46:20.434994+00:00
-- url     : https://prove2.me/theorems/c3a6f00c-6976-4621-a773-296430e50884
-- title:
--   Proof of Proposition 6, Step 2, pp.42–43 — for $e\le\hat e$ the first best is achieved with $(S^*,z^*)$ and a liability $L(e)\in(0,\hat L)$ (corrected: uniqueness for interior priors)
-- statement:
--   Let $(s^*,S^*)$ be first-best standards with $s^*<S^*$ and let $\hat e$ be the critical externality. With the planner committing to $S=S^*$ and $z=z^*$:
--   1. at $e=0$, $s^*$ is a best reply of the firm under strong liability $\bar L(0)$, at every prior;
--   2. at $e=\hat e$, $s^*$ is a best reply of the firm under no liability, at every prior;
--   3. for every $e\in(0,\hat e)$ there is a liability $L(e)$ with
--   $$
--   0<L(e)<\hat L(e)=\frac{v_i\,(v^G_p-v^B_p)}{v^G_p}
--   $$
--   under which $s^*$ is a best reply of the firm at every prior, and for every prior $\sigma_0\in(s^*,S^*)$ it is the only liability in $[0,\bar L(e)]$ with this property;
--   4. consequently, for every $e\in[0,\hat e]$ and every prior, the first best is achieved.
--
--   So for externalities up to $\hat e$ the planner reaches the first best by committing to the socially optimal standards and setting liability to chill excessive research.
--
--   Differences from the source:
--   - correction: L(e) is unique, no restriction on the prior → uniqueness of L(e) for priors σ₀ ∈ (s*, S*); reason: for σ₀ ≥ S* the firm adopts at once under (S*, z*, L) for every L near L(e), so s* is a best reply under all of them
--   - reading: "If e = 0 then strong liability L = L̄ achieves the first best" and "L(e) ∈ (0, L̂)" for e ∈ (0, ê) → clause 1 at e = 0 with L̄(0) (= L̂(0)), clause 3 for e ∈ (0, ê); reason: the page states the two cases separately; at e = 0 the open interval (0, L̂) would exclude the page's own L̄
--   - encoding: ê of Step 1 → ê given by its defining property (IsCriticalExternality, the content of Step 1); reason: Step 1 shows that exactly one ê has this property
--   - reading: values of the stochastic experimentation/stopping problem over stopping rules → closed-form values of threshold policies (rejection s, adoption S, withdrawal z); reason: the paper's own model: fn.17 (p.10) defines (s*, S*) as the maximizer of u¹_p(σ₀, s, S) over thresholds; Lemmas 1–2 (the reduction to thresholds) are not formalized
--   - encoding: beliefs and standards are probabilities q ∈ (0,1) → log-odds σ = log(q/(1−q)) ∈ ℝ; reason: the paper's own change of variables (1), p.8; a monotone bijection, so no instance changes
--   - reading: r₁, r₂ use an undefined μ′₂ (p.33) and R₁, R₂ are not defined (fn.37) → λₙ = 2μₙ²/ρ², r₁,₂ = ½(1 ∓ √(1+4r/λ₂)), R₁,₂ = ½(1 ∓ √(1+4r/λ₁)); reason: derived from the dynamics of p.8 (log-odds drift ±λₙ, variance 2λₙ); reproduces the page's ψ, r₁ + r₂ = 1 and z*
--   - encoding: the closed forms are written for z ≤ S and s < σ₀ < S only → immediate withdrawal (ψ = 1) for S < z, immediate rejection (value 0) for σ₀ ≤ s, immediate adoption (value u²(σ₀, z)) for S ≤ σ₀; reason: the stopping rules at the boundary; both closed forms are continuous there
--   - encoding: standards q ∈ [0,1], including the never-stop standards q = 0, 1 → finite log-odds standards s, S, z ∈ ℝ; reason: the never-stop policies are limits of finite standards, so they never beat the finite ones
--   - encoding: discount rate r ≥ 0 (p.8) → r > 0; reason: every value divides by r (v/r, c/r); r = 0 is undefined, so only undefined cases are excluded
--   - reading: research cost c, no sign stated (p.7) → c > 0; reason: fn.39, p.37 uses "research cost c > 0"; with c = 0 the planner never rejects and the standards of Proposition 1 do not exist
--   - encoding: signal variance ρ² (p.8) → ρ > 0; reason: ρ = 0 makes λₙ undefined (division by zero); only undefined cases are excluded
-- source:
--   Henry–Loseto–Ottaviani, Regulation with Experimentation: Ex Ante Approval, Ex Post Withdrawal, and Liability, working paper (Nov. 2018), sha256 85244fd4…db793c, Proof of Proposition 6, Step 2, pp.42–43 (PDF pp.43–44); L̂ from Proof of Proposition 2, Step 3, p.36

import Mathlib
import Definitions.Def_RegExperiment_Regulation

namespace RegExperiment

/-- **First best for `e ≤ ê`.** Henry–Loseto–Ottaviani, working paper (Nov. 2018), Proof of
Proposition 6, Step 2, pp.42–43.

Let `(s*, S*)` be first-best standards with `s* < S*` and `ê` the critical externality. With the
planner committing to `S = S*` and `z = z*`, for every prior `σ₀`:
1. at `e = 0`, `s*` is a best reply of the firm under strong liability `L̄`;
2. at `e = ê`, `s*` is a best reply of the firm under no liability;
3. for every `e ∈ (0, ê)` there is a liability `L(e)` with `0 < L(e) < L̂(e)` under which `s*` is a
   best reply of the firm at every prior, and for priors `σ₀ ∈ (s*, S*)` it is the only liability
   in `[0, L̄(e)]` with this property;
4. consequently the first best is achieved for every `e ∈ [0, ê]` and every prior.

**Formalization Note** `L̂(e) = v_i(v^G_p − v^B_p)/v^G_p` (p.36). The liability `L(e)` does not
depend on the prior. -/
theorem first_best_low_externality (P : Params) (sS SS ê : ℝ) (hFB : IsFirstBest P sS SS)
    (hlt : sS < SS) (hê : IsCriticalExternality P sS SS ê) :
    (∀ σ₀ : ℝ, FirmBR P 0 σ₀ SS (zstar P) (Lbar P 0) sS) ∧
      (∀ σ₀ : ℝ, FirmBR P ê σ₀ SS (zstar P) 0 sS) ∧
      (∀ e ∈ Set.Ioo (0 : ℝ) ê, ∃ L : ℝ, 0 < L ∧ L < Lhat P e ∧
        (∀ σ₀ : ℝ, FirmBR P e σ₀ SS (zstar P) L sS) ∧
        ∀ L' ∈ Set.Icc (0 : ℝ) (Lbar P e), ∀ σ₀ ∈ Set.Ioo sS SS,
          FirmBR P e σ₀ SS (zstar P) L' sS → L' = L) ∧
      (∀ e ∈ Set.Icc (0 : ℝ) ê, ∀ σ₀ : ℝ, FirstBestAchieved P e σ₀) := by sorry

end RegExperiment
