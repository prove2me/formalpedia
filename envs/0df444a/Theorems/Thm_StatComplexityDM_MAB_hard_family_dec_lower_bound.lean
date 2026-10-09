-- Prove2me | Theorems.Thm_StatComplexityDM_MAB_hard_family_dec_lower_bound
-- name    : StatComplexityDM.MAB.hard_family_dec_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:23:00.568613+00:00
-- url     : https://prove2.me/theorems/77b5836d-21ad-43f1-b10c-c04c46b0d8c8
-- title:
--   Lemma 5.1, (52), p. 31 — an (α, β, δ)-family M′ forces dec_γ(M′, M̄) ≥ α/2 − γ(β/N + δ)
-- statement:
--   Let $\Pi$ be a finite nonempty decision space, $\mathcal{Y}$ a finite outcome space with reward map $r$, $M \mapsto \pi_M$ a selector of maximizers ($\pi_M \in \arg\max_{\pi} f^M(\pi)$ for every model $M$), and let $\mathcal{M}' = \{M_1, \dots, M_N\}$ be an $(\alpha, \beta, \delta)$-family with $\beta \ge 0$ with respect to the reference model $\overline{M}$ (Definition 5.1). Then for every $\gamma > 0$,
--   $$
--   \mathsf{dec}_\gamma(\mathcal{M}', \overline{M}) \ge \frac{\alpha}{2} - \gamma\left( \frac{\beta}{N} + \delta \right),
--   $$
--   where the Decision-Estimation Coefficient (2) is
--   $$
--   \mathsf{dec}_\gamma(\mathcal{M}', \overline{M}) = \inf_{p \in \Delta(\Pi)} \sup_{M \in \mathcal{M}'} \mathbb{E}_{\pi \sim p}\Bigl[ f^M(\pi_M) - f^M(\pi) - \gamma \cdot D^2_{\mathrm{H}}\bigl(M(\pi), \overline{M}(\pi)\bigr) \Bigr].
--   $$
--
--   This is the general device by which the paper lower-bounds the DEC: exhibiting a hard family reduces a min-max lower bound to two pointwise inequalities.
--
--   **Formalization Note** The page's (52) also passes through the dual (Bayesian) DEC; only the primal inequality, which is what Proposition 5.3 uses, is stated. The family predicate includes model class membership and probability models. The paper does not explicitly state $\beta \ge 0$, but its proof multiplies $\sum_i v_i(\pi) \le 1$ by $\beta$; this sign condition is necessary. With $\beta < 0$, identical models, $\alpha=\delta=0$, and $v_i=0$, the printed inequality is false. That $\pi_M$ is a maximizer of $f^M$ (p. 5) is included in the family predicate: the page's proof uses $\mathbb{E}_{i}[\alpha(1-u_i(\pi))] \ge \alpha/2$, which needs $\alpha \ge 0$, and for $\alpha < 0$ the bound follows instead from the nonnegativity of the gaps $f^{M}(\pi_M) - f^{M}(\pi)$; without the argmax property the inequality fails for negative $\alpha$. The decision space is assumed nonempty: for an empty $\Pi$ the simplex is empty and Lean's infimum of the empty set is $0$. Finite alphabets, as throughout this series.
-- source:
--   arXiv:2112.13487v3, Lemma 5.1, (52), p. 31 (proof p. 32)

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_DEC
import Definitions.Def_StatComplexityDM_LowerBound_Core
import Definitions.Def_StatComplexityDM_MAB_HardFamily

namespace StatComplexityDM.MAB

open FoundationsRL.GeneralDM

/-- Lemma 5.1, (52) (arXiv:2112.13487v3, p. 31; proof p. 32), primal form: if
`M′ = {M_1, …, M_N}` (here `Set.range fam`) is an `(α, β, δ)`-family in `𝓜` with respect to `M̄`
(Definition 5.1), then for every `γ > 0`, `dec_γ(M′, M̄) ≥ α/2 − γ(β/N + δ)`, where `dec_γ` is
the DEC (2), `decGf`. The decision space `S` is finite and nonempty, `β ≥ 0`, and `piStar`
selects a maximizer `π_M` of each model's mean reward, as part of the family predicate (p. 5). The nonnegative `β` is
needed for the average information bound in the proof. -/
theorem hard_family_dec_lower_bound {S Y : Type*} [Fintype S] [Fintype Y] [Nonempty S]
    (rew : Y → ℝ) (piStar : (S → Y → ℝ) → S)
    (𝓜 : Set (S → Y → ℝ)) (mbar : S → Y → ℝ) {N : ℕ}
    (fam : Fin N → S → Y → ℝ) (α β δ : ℝ) (hβ : 0 ≤ β)
    (hfam : IsHardFamily 𝓜 rew piStar mbar fam α β δ)
    (γ : ℝ) (hγ : 0 < γ) :
    α / 2 - γ * (β / N + δ) ≤ decGf (Set.range fam) rew piStar γ mbar := by sorry

end StatComplexityDM.MAB
