-- Prove2me | Theorems.Thm_SeqExpDiffusion_proposition_5
-- name    : SeqExpDiffusion.proposition_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:11:50.451236+00:00
-- url     : https://prove2.me/theorems/ddec0919-1a9c-43bd-b63e-63b79c07443d
-- title:
--   Proposition 5 — the two-action value is the closed form (18) (corrected: thresholds at 0 or 1 for a zero reward; squared ℋ)
-- statement:
--   Let $r>0$, $\tilde\sigma>0$, $\gamma=(1+\sqrt{1+8r/\tilde\sigma^2})/2$, and let $\mathscr A=\{a_i,a_j\}$ with $\tilde\beta_i<\tilde\beta_j$, whose rewards cross at some $\hat\delta_{ij}\in(0,1)$, and with $\tilde G_{ij}\ge0$ on $[0,1]$. Then:
--
--   1. there is exactly one quadruple $(\underline\delta_{ij},\bar\delta_{ij},C^0_{ij},C^1_{ij})$ admissible for (18) (thresholds around $\hat\delta_{ij}$, nonnegative constants, value matching and smooth pasting (17));
--   2. the resulting function
--   $$\tilde{\mathcal G}_{ij}(\delta)=\begin{cases}\tilde G_{ij}(\delta)&0\le\delta\le\underline\delta_{ij}\\ C^0_{ij}(1-\delta)^\gamma\delta^{1-\gamma}+C^1_{ij}(1-\delta)^{1-\gamma}\delta^\gamma&\underline\delta_{ij}\le\delta\le\bar\delta_{ij}\\ \tilde G_{ij}(\delta)&\bar\delta_{ij}\le\delta\le1\end{cases}$$
--   is convex on $[0,1]$ and in $\widehat{\mathcal C}^2$;
--   3. it solves the quasi-variational inequalities (15) for the payoff $\tilde G_{ij}$;
--   4. it is the value function of (12) with payoff $\tilde G_{ij}$ ("the verification theorem guarantees that the solution expressed in Proposition 5 is such that $\tilde{\mathcal G}_{ij}=\tilde{\mathcal G}$ when $\mathscr A=\{i,j\}$").
--
--   This is the building block of the general solution: the value with any number of actions is the maximum of these closed forms.
--
--   Differences from the source:
--   - correction: δ̲_ij, δ̄_ij ∈ (0, 1) and C⁰_ij, C¹_ij positive → δ̲_ij = 0 ⟺ C⁰_ij = 0 ⟺ R̃_i ≡ 0 and δ̄_ij = 1 ⟺ C¹_ij = 0 ⟺ R̃_j ≡ 0, with value matching and smooth pasting only at an interior threshold; reason: counterexample: R̃_i ≡ 0, R̃_j(δ) = 2δ − 1, any r, σ̃ > 0 satisfies every assumption (a zero payoff is allowed, Remark 2, p.28), yet matching 0 with slope 0 at any δ̲ > 0 forces C⁰ = C¹ = 0, which cannot meet R̃_j with slope 2
--   - correction: ℋf = ½ σ̃ δ(1−δ) f″ − r f (display (14), p.18) → ℋf = ½ (σ̃ δ(1−δ))² f″ − r f; reason: the printed operator is not the generator of (12); e.g. for σ̃ = 2, r = 1 the closed form (18) does not solve the printed ℋu = 0 (the ratio δ(1−δ)φ₁″/φ₁ of φ₁ = (1−δ)^{1−γ}δ^γ is 2.38 at δ = 0.3 and 2.08 at δ = 0.6), while it solves the squared one; the page itself uses the square on pp.19, 50, 52
--   - reading: "if 𝒜 = {a_i, a_j}" with the standing non-dominance assumption (p.8) → a_i is the left action (β̃_i < β̃_j) and the rewards cross at some δ̂_ij ∈ (0, 1); reason: for two non-dominated actions with distinct rewards this is the same assumption after labelling
--   - reading: "all determined by imposing the value matching and smooth pasting conditions" → the admissible quadruple is unique; reason: the stronger reading of "determined"
--   - encoding: the middle branch on [δ̲_ij, δ̄_ij] → the middle branch on the open interval, G̃_ij at the thresholds; reason: the branches agree at the thresholds by value matching; avoids 0^{1−γ} when δ̲_ij = 0
--   - generalization: stopping times of the filtration 𝔽 of the experimentation history (p.8) → every probability space and every filtration for which the driving motion is Brownian; reason: the paper's setting is one instance, so the statement specializes to it
--   - reading: (12) is silent on the event τ = ∞ → the reward is 0 on {τ = ∞}; reason: the payoffs are bounded, so this changes no supremum relative to finite stopping times
--   - encoding: r and σ̃ are a discount rate and a volatility, with no stated sign → r > 0 and σ̃ > 0; reason: the paper uses both silently (γ needs σ̃ ≠ 0, and r = 0 gives γ = 1); only degenerate cases are excluded
-- source:
--   Araman & Caldentey, Diffusion Approximations for a Class of Sequential Testing Problems, arXiv:2102.07030v3, Proposition 5 and the sentence after it, p.20; (17), p.20; proof, pp.50–51

import Definitions.Def_SeqExpDiffusion_reward
import Definitions.Def_SeqExpDiffusion_pairPayoff
import Definitions.Def_SeqExpDiffusion_IsTwoActionForm
import Definitions.Def_SeqExpDiffusion_pairForm
import Definitions.Def_SeqExpDiffusion_IsHatC2
import Definitions.Def_SeqExpDiffusion_SolvesQVI
import Definitions.Def_SeqExpDiffusion_IsValueFunction

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SeqExpDiffusion

/-- Proposition 5, Araman & Caldentey, *Diffusion Approximations for a Class of Sequential Testing Problems*, arXiv:2102.07030v3, p.20 (corrected): let `γ = (1 + √(1 + 8r/σ̃²))/2`. If `𝒜 = {a_i, a_j}`,
the QVI conditions admit a solution `𝒢̃_ij` given by (18): `G̃_ij(δ)` on `[0, δ̲_ij] ∪ [δ̄_ij, 1]` and
`C⁰ (1 − δ)^γ δ^{1−γ} + C¹ (1 − δ)^{1−γ} δ^γ` on `[δ̲_ij, δ̄_ij]`, with thresholds and constants all
determined by value matching and smooth pasting (17). The function `𝒢̃_ij` is convex and in `Ĉ²`;
by the verification theorem it is the value of the two-action problem (p.20).

Here `a_i` is the left action (`β i < β j`), the two rewards cross at some `δ̂ ∈ (0, 1)` (the
standing non-dominance assumption, p.8, for `𝒜 = {a_i, a_j}`), and `G̃_ij ≥ 0` on `[0, 1]` (p.19).
There is exactly one `(δ̲, δ̄, C⁰, C¹)` satisfying `IsTwoActionForm`, and the resulting (18) is convex
on `[0, 1]`, in `Ĉ²`, solves the QVI (15) for the payoff `G̃_ij`, and is the value function of (12)
with that payoff.

**Formalization Note** Corrected: the page's `δ̲, δ̄ ∈ (0, 1)` and positive constants fail when one
reward is identically `0`; see `IsTwoActionForm`. `ℋ` is the corrected (14). -/
theorem proposition_5 {ι : Type*} (α β : ι → ℝ) (i j : ι) (r σ : ℝ) (hr : 0 < r)
    (hσ : 0 < σ) (hβ : β i < β j)
    (hcross : ∃ δh ∈ Ioo (0 : ℝ) 1, reward α β i δh = reward α β j δh)
    (hpos : ∀ δ ∈ Icc (0 : ℝ) 1, 0 ≤ pairPayoff α β i j δ) :
    ∃ a b C₀ C₁ : ℝ, IsTwoActionForm r σ α β i j a b C₀ C₁ ∧
      (∀ a' b' C₀' C₁' : ℝ, IsTwoActionForm r σ α β i j a' b' C₀' C₁' →
        a' = a ∧ b' = b ∧ C₀' = C₀ ∧ C₁' = C₁) ∧
      ConvexOn ℝ (Icc 0 1) (pairForm r σ α β i j a b C₀ C₁) ∧
      IsHatC2 (pairForm r σ α β i j a b C₀ C₁) ∧
      SolvesQVI r σ (pairPayoff α β i j) (pairForm r σ α β i j a b C₀ C₁) ∧
      IsValueFunction r σ (pairPayoff α β i j) (pairForm r σ α β i j a b C₀ C₁) := by sorry

end SeqExpDiffusion
