-- Prove2me | Theorems.Thm_WassersteinDRO_Duality_lipschitz_regularization_v2
-- name    : WassersteinDRO.Duality.lipschitz_regularization_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:43:27.327992+00:00
-- url     : https://prove2.me/theorems/d93a0fc0-0355-4be3-a02b-0df82e58c9f8
-- title:
--   Theorem 5 — Lipschitz regularization: $R_{\varepsilon,p}(\hat P_N,\ell) \le R(\hat P_N,\ell) + \varepsilon\,\mathrm{Lip}(\ell)$ on Borel $\mathbb{R}^m$
-- statement:
--   Let $E = \mathbb{R}^m$ with an arbitrary norm $\|\cdot\|$ (a finite-dimensional real normed space) and its Borel $\sigma$-algebra, let $\Xi \subseteq E$ be closed, let $\hat P_N$ be a probability distribution on $E$, let $p \in [1,\infty)$ and $\varepsilon \ge 0$, and let $\ell : E \to \mathbb{R}$ be a measurable, upper semicontinuous, $\hat P_N$-integrable loss function. Then the worst-case risk over the type-$p$ Wasserstein ball of radius $\varepsilon$ around $\hat P_N$ is bounded above by the Lipschitz-regularized nominal risk,
--   $$R_{\varepsilon,p}(\hat P_N,\ell) \;\le\; R(\hat P_N,\ell) + \varepsilon\,\mathrm{Lip}(\ell),$$
--   where $\mathrm{Lip}(\ell) = \sup_{\xi \ne \xi'} |\ell(\xi)-\ell(\xi')|/\|\xi-\xi'\| \in [0,\infty]$ and the right-hand side is formed in $[-\infty,\infty]$: if $\ell$ fails to be Lipschitz continuous and $\varepsilon > 0$ the bound is $+\infty$ and the inequality holds trivially, as the paper remarks; if $\varepsilon = 0$ the product $0 \cdot \infty$ is $0$ and the bound $R_{0,p}(\hat P_N,\ell) \le R(\hat P_N,\ell)$ still holds, since the radius-$0$ ball is $\{\hat P_N\}$ or empty.
--
--   **Formalization Note.** The retired version was false because its $\sigma$-algebra on $E$ was a free parameter: with a non-Borel $\sigma$-algebra the transport cost is non-measurable, $W_p(\delta_1,\delta_0) = 0$, and the radius-$0$ ball contains $\delta_1$, which violates the bound at $\varepsilon = 0$. The new statement does the following differently. (i) $E$ is a finite-dimensional real normed space (the paper's $\mathbb{R}^m$ with an arbitrary norm) carrying its Borel $\sigma$-algebra (`[FiniteDimensional ℝ E] [BorelSpace E]`); the retired version quantified over every `MeasurableSpace E`, including $\sigma$-algebras unrelated to the norm, for which the Wasserstein cost is a lower integral and non-constant losses are integrable under no measure. (ii) The worst-case risk is the paper's $\sup_{Q \in \mathcal{B}_{\varepsilon,p}} \mathbb{E}_Q[\ell]$ with the paper's p. 2 convention for non-integrable losses (`worstCaseRisk`/`nominalRisk` v2, valued in $[-\infty,\infty]$) instead of a supremum that silently discarded every $Q$ under which $\ell$ is not integrable. Standing assumptions made explicit: $\Xi$ closed (p. 6); $\hat P_N$ a probability distribution; $p \in [1,\infty)$ and $\varepsilon \ge 0$ (p. 3, 6); the loss is measurable (p. 1) and, by Assumption 1 (p. 9, "tacitly assumed to hold throughout the rest of the paper"), upper semicontinuous and $\hat P_N$-integrable. Losses are taken real-valued, a special case of the paper's extended-real-valued losses that the retired version already made. No correction to the printed source.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, INFORMS TutORials 2019 (arXiv:1908.08729v2, 4 Nov 2024), Theorem 5, p. 9 (setting p. 3, 6; Assumption 1, p. 9)

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_worstCaseRisk_v2
import Definitions.Def_WassersteinDRO_Duality_nominalRisk_v2
import Definitions.Def_WassersteinDRO_Duality_lipschitzModulus

open MeasureTheory

namespace WassersteinDRO.Duality

/-- Theorem 5 (Lipschitz regularization), Kuhn, Mohajerin Esfahani, Nguyen &
Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization*, INFORMS TutORials
2019 (arXiv:1908.08729v2), p. 9: the worst-case risk (6) of any fixed loss function `ℓ ∈ L` is
bounded above by the Lipschitz-regularized nominal risk, `Rε,p(PN,ℓ) ≤ R(PN,ℓ) + ε·Lip(ℓ)`.

Setting (p. 3, 6, 9): `E` is `ℝ^m` with an arbitrary norm — a finite-dimensional real normed
space — carrying its Borel σ-algebra (`[BorelSpace E]`); `Ξ ⊆ E` is closed; `PN` is a
probability distribution; `p ∈ [1,∞)`, `ε ≥ 0`. The loss satisfies the paper's standing
conventions: `ℓ` is measurable (p. 1) and, by Assumption 1 (p. 9, "tacitly assumed to hold
throughout the rest of the paper"), upper semicontinuous and `PN`-integrable. The right-hand
side is formed in `EReal`/`ℝ≥0∞`, so a non-Lipschitz `ℓ` (`Lip(ℓ) = ∞`) with `ε > 0` makes the
bound `+∞` ("trivially satisfied", p. 9); with `ε = 0` the product is `0·∞ = 0` and the bound
`R_{0,p}(PN,ℓ) ≤ R(PN,ℓ)` still holds, since the radius-`0` ball is `{PN}` or empty.

Corrected from the retired `lipschitz_regularization`: the σ-algebra was a free
`[MeasurableSpace E]` unrelated to the norm topology (so `W_p` was not a metric and the bound
failed at `ε = 0`), `E` was not finite-dimensional, measurability/upper semicontinuity of `ℓ`
were missing, and the worst-case risk dropped non-integrable `Q` instead of using the paper's
convention `E_Q[ℓ] ∈ {-∞,+∞}` (now `worstCaseRisk`/`nominalRisk` v2). -/
theorem lipschitz_regularization_v2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ε p : ℝ) (hε : 0 ≤ ε) (hp : 1 ≤ p) (Ξ : Set E) (hΞcl : IsClosed Ξ)
    (PN : Measure E) [IsProbabilityMeasure PN]
    (ℓ : E → ℝ) (hℓm : Measurable ℓ) (hℓusc : UpperSemicontinuous ℓ) (hℓ : Integrable ℓ PN) :
    worstCaseRisk ε p Ξ PN ℓ ≤
      nominalRisk PN ℓ + ((ENNReal.ofReal ε * lipschitzModulus ℓ : ENNReal) : EReal) := by sorry

end WassersteinDRO.Duality
