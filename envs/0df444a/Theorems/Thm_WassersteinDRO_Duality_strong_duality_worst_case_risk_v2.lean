-- Prove2me | Theorems.Thm_WassersteinDRO_Duality_strong_duality_worst_case_risk_v2
-- name    : WassersteinDRO.Duality.strong_duality_worst_case_risk_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:43:52.540978+00:00
-- url     : https://prove2.me/theorems/2ac0af44-3d4d-4f69-b910-bfa67efa2622
-- title:
--   Theorem 7 — strong duality $R_{\varepsilon,p}(\hat P_N,\ell) = \inf_{\gamma\ge0} \mathbb{E}_{\hat P_N}[\ell_\gamma] + \gamma\varepsilon^p$ on Borel $\mathbb{R}^m$, usc losses, $\varepsilon > 0$
-- statement:
--   Let $E = \mathbb{R}^m$ with an arbitrary norm (a finite-dimensional real normed space) and its Borel $\sigma$-algebra, let $\Xi \subseteq E$ be closed, let $\hat P_N$ be a probability distribution supported on $\Xi$ ($\hat P_N(\Xi^c) = 0$), let $p \in [1,\infty)$ and $\varepsilon > 0$, and let $\ell : E \to \mathbb{R}$ be a measurable, upper semicontinuous, $\hat P_N$-integrable loss function. Then the worst-case risk over the type-$p$ Wasserstein ball satisfies the strong duality
--   $$R_{\varepsilon,p}(\hat P_N,\ell) \;=\; \inf_{\gamma \ge 0}\ \mathbb{E}_{\hat P_N}[\ell_\gamma(\xi)] + \gamma\,\varepsilon^p,\qquad \ell_\gamma(\xi) = \sup_{z \in \Xi}\ \ell(z) - \gamma\|z-\xi\|^p,$$
--   where $\ell_\gamma$ is the Moreau–Yosida regularization of $\ell$, valued in $(-\infty,+\infty]$ on $\Xi$ (it is $+\infty$ where $\ell$ grows faster than $\|\cdot\|^p$), $\mathbb{E}_{\hat P_N}[\ell_\gamma] \in (-\infty,+\infty]$ is its extended expectation (finite negative part, since $\ell_\gamma \ge \ell$ on $\Xi$), and the identity is read in $[-\infty,\infty]$: both sides may be $+\infty$ simultaneously. The right-hand side is the Lagrangian dual of the worst-case risk evaluation problem, $\gamma$ being the multiplier of the Wasserstein constraint.
--
--   **Formalization Note.** The retired version was false because its $\sigma$-algebra on $E$ was a free parameter: with the trivial $\sigma$-algebra no non-constant loss is integrable under any probability measure, so the integrability-guarded worst-case risk was $-\infty$ while the dual side was $\ge -\|\ell\|_\infty$. The new statement does the following differently. (i) $E$ is a finite-dimensional real normed space with its Borel $\sigma$-algebra (`[FiniteDimensional ℝ E] [BorelSpace E]`). (ii) The loss class is the paper's: an arbitrary measurable, upper semicontinuous, $\hat P_N$-integrable $\ell$ (p. 1 and Assumption 1, p. 9), instead of the retired narrowing to bounded continuous functions; accordingly $\ell_\gamma$ is extended-real-valued (`moreauYosida` v2) and $\mathbb{E}_{\hat P_N}[\ell_\gamma]$ is the extended expectation with the paper's p. 2 convention (`erealExpectation`). (iii) The worst-case risk is the paper's $\sup_{Q \in \mathcal{B}_{\varepsilon,p}} \mathbb{E}_Q[\ell]$ with that same convention (`worstCaseRisk`/`nominalRisk` v2) instead of a supremum discarding non-integrable $Q$. (iv) **Correction to the printed source: the radius is required to be strictly positive.** The paper's framework allows $\varepsilon \ge 0$ (p. 6), but at $\varepsilon = 0$ the printed identity fails: for $p = 1$, $\Xi = \mathbb{R}$, $\hat P_N = \delta_0$ and $\ell(\xi) = \xi^2$ (convex, continuous, $\delta_0$-integrable), the ball $\mathcal{B}_{0,1}(\delta_0)$ is $\{\delta_0\}$ because $W_1$ is a metric (p. 3), so the left-hand side is $0$, whereas $\ell_\gamma(0) = \sup_z z^2 - \gamma|z| = +\infty$ for every $\gamma \ge 0$ and the right-hand side is $+\infty$. Strong duality for every upper semicontinuous $\hat P_N$-integrable loss is the standard result for $\varepsilon > 0$ (Gao–Kleywegt, *Math. Oper. Res.* 2023, Thm. 1; Blanchet–Murthy, *Math. Oper. Res.* 2019, Thm. 1), which is what is stated here; the paper's own remark that (10) is solvable "for any $\varepsilon > 0$" shows the same reading. Standing assumptions made explicit: $\Xi$ closed (p. 6); $\hat P_N \in \mathcal{P}(\Xi)$ (the ambiguity set is a ball in $\mathcal{P}(\Xi)$ centred at $\hat P_N$, p. 6; it also forces $\Xi \ne \emptyset$); $\hat P_N$ a probability distribution; $p \in [1,\infty)$; the loss measurable (p. 1) and, by Assumption 1 (p. 9), upper semicontinuous and $\hat P_N$-integrable. Losses are taken real-valued, a special case of the paper's extended-real-valued losses that the retired version already made. No growth or boundedness condition on $\ell$ is imposed.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, INFORMS TutORials 2019 (arXiv:1908.08729v2, 4 Nov 2024), Theorem 7, p. 10, eq. (10) (setting p. 3, 6; Assumption 1, p. 9) — corrected transcription: the radius is restricted to ε > 0, since the printed identity fails at ε = 0 for losses growing faster than ‖·‖^p (standard form: Gao & Kleywegt, Math. Oper. Res. 48 (2023), Thm. 1; Blanchet & Murthy, Math. Oper. Res. 44 (2019), Thm. 1)

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_worstCaseRisk_v2
import Definitions.Def_WassersteinDRO_Duality_moreauYosida_v2
import Definitions.Def_WassersteinDRO_Duality_erealExpectation

open MeasureTheory

namespace WassersteinDRO.Duality

/-- Theorem 7 (Strong duality), Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh,
*Wasserstein Distributionally Robust Optimization*, INFORMS TutORials 2019
(arXiv:1908.08729v2), p. 10, eq. (10) — the goal theorem: the worst-case risk (6) of any fixed
`ℓ ∈ L` satisfies `Rε,p(PN,ℓ) = inf_{γ≥0} E_{PN}[ℓγ(ξ)] + γ·ε^p`, where
`ℓγ(ξ) = sup_{z∈Ξ} ℓ(z) - γ‖z-ξ‖^p` is the Moreau-Yosida regularization of `ℓ`.

Setting (p. 3, 6, 9): `E` is `ℝ^m` with an arbitrary norm (finite-dimensional real normed
space) with its Borel σ-algebra; `Ξ ⊆ E` is closed and contains the support of the nominal
distribution (`PN Ξᶜ = 0`, i.e. `PN ∈ P(Ξ)`, the paper's framework for every ambiguity set
`Bε,p(PN) ⊆ P(Ξ)` centred at `PN`; it forces `Ξ ≠ ∅`); `PN` is a probability distribution;
`p ∈ [1,∞)`. The loss satisfies the standing conventions: measurable (p. 1) and, by
Assumption 1 (p. 9), upper semicontinuous and `PN`-integrable. No boundedness or growth
condition is imposed on `ℓ`: `ℓγ` is `EReal`-valued (it is `+∞` where `ℓ` grows faster than
`‖·‖^p`), and `E_{PN}[ℓγ]` is the extended expectation with the paper's convention of p. 2
(`erealExpectation`); since `ℓγ ≥ ℓ` on `Ξ`, it lies in `(-∞, +∞]`, and both sides of (10)
may equal `+∞` simultaneously.

**Correction to the printed source: `ε > 0`.** The paper allows `ε ≥ 0` (p. 6). At `ε = 0` the
printed identity is false: for `p = 1`, `Ξ = ℝ`, `PN = δ₀`, `ℓ(ξ) = ξ²` (convex, continuous,
`δ₀`-integrable) the ball `B_{0,1}(δ₀)` is `{δ₀}` (`W₁` is a metric, p. 3), so the left-hand
side is `0`, while `ℓγ(0) = sup_z z² - γ|z| = +∞` for every `γ ≥ 0`, so the right-hand side
is `+∞`. Strong duality holds for every usc `PN`-integrable loss when `ε > 0` (Gao &
Kleywegt, *Math. Oper. Res.* 2023, Thm. 1; Blanchet & Murthy, *Math. Oper. Res.* 2019,
Thm. 1), which is the form stated here.

Corrected from the retired `strong_duality_worst_case_risk`: the σ-algebra was a free
`[MeasurableSpace E]` (with the trivial σ-algebra no non-constant `ℓ` was integrable under
any `Q`, so the guarded worst-case risk collapsed to `-∞`), `E` was not finite-dimensional,
`ℓ` was narrowed to bounded continuous functions (an extra hypothesis beyond Assumption 1),
the degenerate radius `ε = 0` was included, and the worst-case risk dropped non-integrable
`Q` instead of using the paper's convention (now `worstCaseRisk`/`nominalRisk` v2). -/
theorem strong_duality_worst_case_risk_v2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ε p : ℝ) (hε : 0 < ε) (hp : 1 ≤ p) (Ξ : Set E) (hΞcl : IsClosed Ξ)
    (PN : Measure E) [IsProbabilityMeasure PN] (hPNΞ : PN Ξᶜ = 0)
    (ℓ : E → ℝ) (hℓm : Measurable ℓ) (hℓusc : UpperSemicontinuous ℓ) (hℓ : Integrable ℓ PN) :
    worstCaseRisk ε p Ξ PN ℓ =
      ⨅ (γ : ℝ) (_ : 0 ≤ γ),
        erealExpectation PN (moreauYosida Ξ ℓ p γ) + ((γ * ε ^ p : ℝ) : EReal) := by sorry

end WassersteinDRO.Duality
