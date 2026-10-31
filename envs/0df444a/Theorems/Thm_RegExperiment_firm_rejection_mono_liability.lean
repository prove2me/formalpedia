-- Prove2me | Theorems.Thm_RegExperiment_firm_rejection_mono_liability
-- name    : RegExperiment.firm_rejection_mono_liability
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:46:36.896123+00:00
-- url     : https://prove2.me/theorems/8db9e2ab-3c45-4770-ac5a-cba7ce9ccc3b
-- title:
--   Proof of Proposition 6, Step 2, p.43 — the firm's rejection standard rises strictly with liability $L$
-- statement:
--   Fix an externality $e\in[0,1]$, a prior $\sigma_0$, an adoption standard $S>\sigma_0$ and a withdrawal standard $z$. Let $0\le L<L'\le\bar L(e)$. If $s<\sigma_0$ is a best reply of the firm under liability $L$ (so the firm experiments) and $s'$ is a best reply under $L'$, then
--   $$
--   s<s'.
--   $$
--   This is the page's "$\partial^2 u^1_i/\partial s\,\partial L>0$": liability lowers the firm's payoff in the bad state and makes it abandon research earlier. It makes the first-best liability $L(e)$ of Step 2 unique.
--
--   Differences from the source:
--   - reading: ∂²u¹_i/∂s∂L > 0 ("this liability level is unique") → strict increase of the firm's best replies in L; reason: the derivative sign is the statement about the best reply it is used for
--   - reading: the firm's rejection standard s_pp(L), with no prior mentioned → a best reply s < σ₀ at a prior σ₀ < S (the firm experiments); reason: at σ₀ ≥ S (adopt at once) or when the firm rejects at once every s on one side of σ₀ is a best reply, so the comparison would be false
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
--   Henry–Loseto–Ottaviani, Regulation with Experimentation: Ex Ante Approval, Ex Post Withdrawal, and Liability, working paper (Nov. 2018), sha256 85244fd4…db793c, Proof of Proposition 6, Step 2, p.43 (PDF p.44)

import Mathlib
import Definitions.Def_RegExperiment_Regulation

namespace RegExperiment

/-- **The firm's rejection standard rises with liability.** Henry–Loseto–Ottaviani, working paper
(Nov. 2018), Proof of Proposition 6, Step 2, p.43 ("this liability level is unique since
`∂u¹_i/∂s∂L > 0`").

Fix an externality `e ∈ [0, 1]`, a prior `σ₀`, an adoption standard `S > σ₀` and a withdrawal
standard `z`. Let `0 ≤ L < L' ≤ L̄(e)`. If `s < σ₀` is a best reply of the firm under liability `L`
(the firm experiments) and `s'` is a best reply under `L'`, then `s < s'`.

**Formalization Note** The page's derivative sign is stated as strict monotonicity of the firm's
best replies. The prior must lie below `S`: at `σ₀ ≥ S` the firm adopts at once and its rejection
standard is not determined. -/
theorem firm_rejection_mono_liability (P : Params) (e σ₀ S z L L' s s' : ℝ)
    (he : 0 ≤ e) (he1 : e ≤ 1) (hL : 0 ≤ L) (hLL' : L < L') (hL' : L' ≤ Lbar P e)
    (hσS : σ₀ < S) (hs : FirmBR P e σ₀ S z L s) (hsσ : s < σ₀)
    (hs' : FirmBR P e σ₀ S z L' s') :
    s < s' := by sorry

end RegExperiment
