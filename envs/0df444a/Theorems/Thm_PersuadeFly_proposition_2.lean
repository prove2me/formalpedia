-- Prove2me | Theorems.Thm_PersuadeFly_proposition_2
-- name    : PersuadeFly.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:32:06.310812+00:00
-- url     : https://prove2.me/theorems/2d15499e-6554-4951-8dba-168939d45a04
-- title:
--   Proposition 2, p.25 — $\mathsf{Gap}(\mu,\mathsf B_1(\mu,\epsilon))\le\frac{4}{p^2D}\,\epsilon$
-- statement:
--   Let the instance satisfy the regularity conditions (Assumption 1) with radius $D$. Let $\mu\in\Delta(\Omega)$ and $p>0$ with $\min_\omega\mu(\omega)\ge p$. Then for all $\epsilon\ge0$,
--   $$
--   \mathsf{Gap}\big(\mu,\mathsf B_1(\mu,\epsilon)\big)\le\frac{4}{p^2D}\,\epsilon .
--   $$
--   With $p=p_0$ and $\mu\in\mathcal B_0$ this is the paper's Proposition 2. The cost of robust persuasion is at most linear in the radius of the ball; without the regularity conditions it can be a constant (Appendix A.1 of the paper).
--
--   Differences from the source:
--   - generalization: μ ∈ B₀ and the bound 4ϵ/(p₀²D) → any μ ∈ Δ(Ω) with min_ω μ(ω) ≥ p > 0 and the bound 4ϵ/(p²D); reason: p = p₀ with μ ∈ B₀ gives the printed statement; the proof of Lemma 5 (p.41) applies "the same argument" at p = p₀/2 to γ_t ∉ B₀
--   - generalization: D the largest radius in Assumption 1 → any radius D for which Assumption 1.1 holds; reason: the largest radius is admissible, so the printed statement is the instance D = largest
-- source:
--   Zu, Iyer, Xu, Learning to Persuade on the Fly: Robustness Against Ignorance, arXiv:2102.10156v2, Proposition 2, p.25

import Mathlib
import Definitions.Def_PersuadeFly_IsRegular
import Definitions.Def_PersuadeFly_gap

namespace PersuadeFly

/-- **Proposition 2 (cost of robust persuasion is linear).** Zu, Iyer, Xu, *Learning to Persuade on the Fly: Robustness Against Ignorance*, arXiv:2102.10156v2, Proposition 2, p.25: for any instance
that satisfies the regularity conditions, for all `μ ∈ B₀` and all `ϵ ≥ 0`,
`Gap(μ, B₁(μ, ϵ)) ≤ (4 / (p₀² D)) ϵ`.

**Formalization Note** Stated for every `μ ∈ Δ(Ω)` with `min_ω μ(ω) ≥ p > 0`, with bound
`(4 / (p² D)) ϵ`. Taking `p = p₀` and `μ ∈ B₀` gives the printed statement; the proof of Lemma 5 (p.41)
uses "the same argument" at `p = p₀ / 2` for `γ_t`, which need not lie in `B₀`. -/
theorem proposition_2 {Ω A : Type} [Fintype Ω] [Nontrivial Ω] [Fintype A] [Nontrivial A]
    (I : Instance Ω A) (D p0 : ℝ) (hreg : IsRegular I D p0)
    (μ : Ω → ℝ) (hμ : μ ∈ stdSimplex ℝ Ω) (p : ℝ) (hp : 0 < p) (hμp : ∀ ω, p ≤ μ ω)
    (ϵ : ℝ) (hϵ : 0 ≤ ϵ) :
    gap I μ (ball1 μ ϵ) ≤ 4 / (p ^ 2 * D) * ϵ := by sorry

end PersuadeFly
