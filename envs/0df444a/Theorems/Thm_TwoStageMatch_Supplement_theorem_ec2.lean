-- Prove2me | Theorems.Thm_TwoStageMatch_Supplement_theorem_ec2
-- name    : TwoStageMatch.Supplement.theorem_ec2
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:14:55.903923+00:00
-- url     : https://prove2.me/theorems/a944956f-ea62-5d94-8860-d32d328ef673
-- title:
--   Theorem EC.2: Algorithm 4 is $\min_{t\in[\gamma,1]}(t+\beta(1-t)^2)$-competitive against $\mathrm{OPT}_{\mathrm{offline}}$ (corrected: printed constant $\gamma+\beta(1-\gamma)^2$)
-- statement:
--   Let $g:\mathbb R\to\mathbb R$ be differentiable, monotone increasing and strictly convex, and let $\gamma,\beta\in[0,1]$. On every unweighted instance ($w_j=1$ for all $j$) satisfying Assumption EC.1 with parameter $\gamma$, every run of Algorithm 4 (Algorithm 1's first stage, then a matching $M_2$ between $\tilde D_2$ and the unmatched supplies of size at least $\beta$ times the maximum) satisfies
--   $$\mathbb E\big[|M_1\cup M_2|\big]\ \ge\ \Big(\min_{t\in[\gamma,1]}\big(t+\beta(1-t)^2\big)\Big)\cdot\mathrm{OPT}_{\mathrm{offline}}.$$
--
--   The minimum equals the printed constant $\gamma+\beta(1-\gamma)^2$ exactly when $\gamma\ge1-1/(2\beta)$, in particular always when $\beta\le1/2$. The bound shows how a lower bound on the first stage's share of the maximum matching improves the guarantee of an approximate second stage.
--
--   Differences from the source:
--   - correction: Algorithm 4 is (γ + β(1 − γ)²)-competitive against OPT_offline → the constant min_{t∈[γ,1]} (t + β(1 − t)²); reason: the printed statement is false for γ < 1 − 1/(2β): with D₁ = {a}, S = {1, 2}, a adjacent to both, D₂ = {b} adjacent to 1, π_b = 1 and β = 1, Algorithm 4 gets 3/2 against OPT_offline = 2, Assumption EC.1 holds for every γ ≤ 1/2, and γ + (1 − γ)² > 3/4 for γ < 1/2. The proof (p.ec12) bounds the first stage by |S⁽⁰⁾| + γ Σ_l |S⁽ˡ⁾ ∩ O| and treats the assumption as an equality; with the realization's own ratio t ≥ γ the same steps give t + β(1 − t)², whose minimum over [γ, 1] is the repaired constant (3/4 in the example)
--   - encoding: Assumption EC.1: |M₁*|/|M*| ≥ γ for each realization D̃₂ → γ·|M*| ≤ |M₁*| for every A ⊆ D₂ of positive probability; reason: avoids 0/0 when |M*| = 0, where the ratio is undefined; a realization is an outcome of positive probability
--   - reading: a β-approximately maximum matching M₂ between D̃₂ and the remaining unmatched vertices of S → a rule choosing, for each first-stage matching and realization, a matching of size at least β times the maximum; reason: a randomized choice is a mixture of such rules and its value is the same mixture
--   - encoding: (γ + β(1 − γ)²)-competitive → ALG ≥ c·OPT_offline on every instance satisfying the assumption, for every run; reason: a competitive ratio over a class of instances is this per-instance inequality
-- source:
--   Feng, Niazadeh & Saberi, Two-stage Stochastic Matching and Pricing with Applications to Ride Hailing, arXiv:2210.11648v1, Theorem EC.2, p.ec9; Assumption EC.1, p.ec9; Algorithm 4, p.ec10; proof pp.ec10–ec13

import Mathlib
import Definitions.Def_TwoStageMatch_Supplement_Algorithm4

namespace TwoStageMatch.Supplement

/-- **Theorem EC.2, corrected** (Feng, Niazadeh & Saberi, arXiv:2210.11648v1, p.ec9; proof
pp.ec10–ec13). Printed: for any differentiable, monotone increasing and strictly convex function
`g : ℝ → ℝ`, under Assumption EC.1 with `γ ∈ [0, 1]`, Algorithm 4 is `(γ + β(1 − γ)²)`-competitive
against `OPT_offline`.

Stated with the repaired constant: on every unweighted instance (`w_j = 1`) satisfying Assumption
EC.1 with `γ ∈ [0, 1]`, for `β ∈ [0, 1]` and every run of Algorithm 4,
`𝔼[|M₁ ∪ M₂|] ≥ (min_{t ∈ [γ, 1]} (t + β(1 − t)²)) · OPT_offline`.

The minimum equals the printed `γ + β(1 − γ)²` exactly when `γ ≥ 1 − 1/(2β)` (always when
`β ≤ 1/2`). For smaller `γ` the printed statement is false: with `D₁ = {a}`, `S = {1, 2}`, `a`
adjacent to both, `D₂ = {b}` adjacent to `1`, `π_b = 1`, `β = 1`, Algorithm 4 gets `3/2` against
`OPT_offline = 2`, Assumption EC.1 holds for every `γ ≤ 1/2`, and `γ + (1 − γ)² > 3/4` for
`γ < 1/2`; the repaired constant is `3/4` there.

**Formalization Note.** The minimum is `⨅ t ∈ [γ, 1]`, a nonempty compact set on which the
function is bounded below, so it is attained. Algorithm 4's runs and Assumption EC.1 are as in
`Def_TwoStageMatch_Supplement_Algorithm4`. -/
theorem theorem_ec2 (g : ℝ → ℝ) (hgd : Differentiable ℝ g) (hgm : Monotone g)
    (hgc : StrictConvexOn ℝ Set.univ g) (γ β : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    {D₁ D₂ S : Type*} [Fintype D₁] [Fintype D₂] [Fintype S] [DecidableEq D₁] [DecidableEq D₂]
    [DecidableEq S] (I : Instance D₁ D₂ S) (hw : ∀ j, I.w j = 1) (hA : AssumptionEC1 I γ)
    (r : Run4 I g β) :
    (⨅ t : Set.Icc γ 1, ((t : ℝ) + β * (1 - (t : ℝ)) ^ 2)) * optOffline I ≤ r.value := by sorry

end TwoStageMatch.Supplement
