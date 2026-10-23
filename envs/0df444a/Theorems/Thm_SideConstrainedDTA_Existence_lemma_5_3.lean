-- Prove2me | Theorems.Thm_SideConstrainedDTA_Existence_lemma_5_3
-- name    : SideConstrainedDTA.Existence.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:07:42.365596+00:00
-- url     : https://prove2.me/theorems/00982b9a-e5ac-46b9-87de-e828b75cb79a
-- title:
--   Lemma 5.3, p. 22 — if every nonzero γ-deviation in A_p(h*) dominates a nonzero one in A′_p(h*), an SCDE w.r.t. A′ is an SCDE w.r.t. A
-- statement:
--   Let $S$ be a constraint set, $\Phi$ an effective walk delay operator, and $A_p$, $A'_p$ two correspondences of admissible $\gamma$-deviations. Let $h^*$ be such that for every walk $p$:
--
--   for every $(q,\gamma,\Delta)\in A_p(h^*)$ with $\gamma\ne0$ (measurable, non-negative, $\int_{t_0}^{t_f}\gamma>0$) there is $(q,\gamma',\Delta)\in A'_p(h^*)$ with $\gamma'$ measurable, $\int_{t_0}^{t_f}\gamma'>0$ and
--   $$0\le\gamma'\le\gamma .$$
--
--   If $h^*$ is a side-constrained dynamic equilibrium (SCDE) with respect to $S$ and $A'$, then it is also an SCDE with respect to $S$ and $A$.
--
--   In words: allowing fewer deviations gives a weaker equilibrium notion. This comparison is how the paper orders its equilibrium concepts (Proposition 7.3).
--
--   **Formalization Note.** For non-negative $\gamma$ supported in $[t_0,t_f]$, "$\gamma\ne0$" in $L^2$ is read as $\int_{t_0}^{t_f}\gamma>0$; "$\gamma'\le\gamma$" is pointwise on the representatives, with $\gamma'\ge0$. The hypothesis is required only for measurable, non-negative $\gamma$, which are the only ones the admissible-deviation sets $U_p$ use.
-- source:
--   Graf, Harks, Side-Constrained Dynamic Traffic Equilibria, arXiv:2211.03194v3, p. 22, Lemma 5.3

import Mathlib
import Definitions.Def_SideConstrainedDTA_Existence_Setting

open MeasureTheory Set Filter Topology

namespace SideConstrainedDTA.Existence

/-- Lemma 5.3, p. 22: if every admissible `(q, γ, Δ) ∈ A_p(h*)` with `γ ≠ 0` has a non-zero
`(q, γ', Δ) ∈ A'_p(h*)` with `0 ≤ γ' ≤ γ`, then an SCDE w.r.t. `S` and `A'` is an SCDE w.r.t.
`S` and `A`. -/
theorem lemma_5_3 {I W E : Type*} [Fintype I] [Fintype W] [DecidableEq I] [DecidableEq W]
    (N : Model I W E) (hN : N.Basic) (Φ : (W → ℝ → ℝ) → W → ℝ → ℝ)
    (S : (W → ℝ → ℝ) → Prop) (A A' : Corr W) (hs : W → ℝ → ℝ)
    (hcond : ∀ p, ∀ x ∈ A p hs, Measurable x.2.1 → (∀ s, 0 ≤ x.2.1 s) →
      0 < ∫ s in Icc N.t0 N.tf, x.2.1 s →
      ∃ γ' : ℝ → ℝ, (x.1, γ', x.2.2) ∈ A' p hs ∧ Measurable γ' ∧
        (∀ s, 0 ≤ γ' s ∧ γ' s ≤ x.2.1 s) ∧ 0 < ∫ s in Icc N.t0 N.tf, γ' s) :
    IsSCDE N Φ S A' hs → IsSCDE N Φ S A hs := by sorry

end SideConstrainedDTA.Existence
