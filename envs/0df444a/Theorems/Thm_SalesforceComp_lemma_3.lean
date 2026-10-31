-- Prove2me | Theorems.Thm_SalesforceComp_lemma_3
-- name    : SalesforceComp.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:25:21.968433+00:00
-- url     : https://prove2.me/theorems/05bd6977-e8e4-4031-9399-5ff573dfe4ed
-- title:
--   Lemma 3, p. 22 — expected sales $S(r,Q)$ is jointly concave
-- statement:
--   Work in the model of §2 with Assumption 1 (the `Model` definition of this mission): output cost $K(r,\theta)=C(E(r,\theta))$, expected demand $D$, expected sales $S$, inverse hazard rate $H$ on the type support $[\underline\theta,\bar\theta]$, and the virtual surplus $M(r,Q,\theta)=pS(r,Q)-(c+h)Q-K(r,\theta)+K_2(r,\theta)H(\theta)$.
--
--   The expected realized sales
--   $$S(r,Q)=\mathbb E_\varepsilon\big[\min\{d(r,\varepsilon),Q\}\big]$$
--   is a concave function of $(r,Q)$ on $[0,\infty)\times\mathbb R$.
--
--   Concavity of $S$ makes the virtual surplus $M$ concave in $(r,Q)$, which is what turns the first-order system (1) into a maximization in Proposition 1.
--
--   **Formalization Note** Only concavity is stated, as in the lemma. The paper's proof also asserts $S_{22}<0$, which fails when the density of $\varepsilon$ vanishes at the relevant point; the statement does not need it.
--
--   Differences from the source:
--   - generalization: Assumption 1 (C), (D), (E), p. 7, printed without a domain → C, d, E are C³ on ℝ, ℝ², ℝ²; the sign conditions are required only on the domain of the model: E at outputs r ≥ 0 and types θ ∈ [θ̲, θ̄], C at the efforts E(r, θ) these reach, d at outputs r ≥ 0 and G-almost every ε; reason: the action set is r ≥ 0 (p. 9) and the type support is [θ̲, θ̄]; no statement looks outside them, so any reading of the assumption on a domain containing this one specializes to it
--   - encoding: output R(e, θ), with E defined by R(E(r, θ), θ) = r (p. 7) → E is a primitive of the model; R does not appear; reason: the paper says the reformulated model in (r, K) "will be our focus throughout the paper", and Assumption 1 puts no condition on R
--   - reading: H(θ) = (1 − F(θ))/f(θ) decreases in θ (p. 7) → H is antitone (weakly decreasing) on [θ̲, θ̄]; reason: the proof of Proposition 1 uses only H′ ≤ 0
--   - generalization: ε has a distribution G with density g, and all functions are C³ (p. 7) → G is any probability measure on ℝ absolutely continuous w.r.t. Lebesgue measure; no smoothness of g; reason: every C³ density is such a G, so the statement specializes to the source's
--   - encoding: Θ has density f on [θ̲, θ̄]; H divides by f → f measurable, integrable on [θ̲, θ̄] with total mass 1, and f > 0 on [θ̲, θ̄]; reason: the positivity excludes only the undefined values of H
--   - encoding: D(r) = E_ε[d(r, ε)] (p. 8) → ε ↦ d(r, ε) is G-integrable for every r ≥ 0; reason: the expectation is presupposed by its definition
--   - reading: unit price p (p. 6) → p > 0; reason: a unit price; implicit in the paper
--   - encoding: partial derivatives as numbered subscripts (p. 7) → deriv of one-variable slices (pd1, pd2); reason: all functions concerned are differentiable, so the values agree
-- source:
--   Song–Lai–Xiao, Optimal Salesforce Compensation, MSOM (2024), doi:10.1287/msom.2022.0400, Appendix A, Lemma 3, p. 22

import Mathlib
import Definitions.Def_SalesforceComp_Model

open MeasureTheory

namespace SalesforceComp

open Model

/-- **Lemma 3** (concavity of expected sales), Song–Lai–Xiao, MSOM (2024),
doi:10.1287/msom.2022.0400, Appendix A, Lemma 3, p. 22: the expected realized sales
`S(r, Q) = E_ε[min{d(r, ε), Q}]` is concave in `(r, Q)`.

**Formalization Note.** Concavity is joint, for outputs `r ≥ 0` and every `Q`. Only concavity is
stated: the proof's claim `S₂₂ < 0` fails when the density of `ε` vanishes at `l(r, Q)`. -/
theorem lemma_3 (M : Model) :
    ConcaveOn ℝ (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) (fun x : ℝ × ℝ => M.S x.1 x.2) := by sorry

end SalesforceComp
