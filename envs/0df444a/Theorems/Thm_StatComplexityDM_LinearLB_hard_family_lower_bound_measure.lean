-- Prove2me | Theorems.Thm_StatComplexityDM_LinearLB_hard_family_lower_bound_measure
-- name    : StatComplexityDM.LinearLB.hard_family_lower_bound_measure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:21:26.439565+00:00
-- url     : https://prove2.me/theorems/96f1fc23-15eb-49c6-aac6-5408ca63796a
-- title:
--   Lemma 5.1, (52), p. 31 — an (α, β, δ)-family forces sup_i E_p[g_i − γD_i] ≥ α/2 − γ(β/N + δ), for any decision distribution p on a general space
-- statement:
--   Let $(\Pi, \mathscr{P})$ be a measurable decision space, $p$ a probability measure on it, $N \ge 2$, and $\alpha, \beta \ge 0$, $\delta \in \mathbb{R}$, $\gamma > 0$. Let $g_i, D_i, u_i, v_i : \Pi \to \mathbb{R}$ ($i = 1, \dots, N$) be $p$-integrable functions such that, for every $i$ and every $\pi \in \Pi$:
--
--   1. (regret property) $g_i(\pi) \ge \alpha \, (1 - u_i(\pi))$, with $\sum_{i=1}^N u_i(\pi) \le N/2$;
--   2. (information property) $D_i(\pi) \le \beta \, v_i(\pi) + \delta$, with $\sum_{i=1}^N v_i(\pi) \le 1$.
--
--   Then some index $i$ satisfies
--   $$
--   \mathbb{E}_{\pi \sim p}\bigl[ g_i(\pi) - \gamma\, D_i(\pi) \bigr] \ge \frac{\alpha}{2} - \gamma \left( \frac{\beta}{N} + \delta \right).
--   $$
--
--   With $g_i(\pi) = f^{M_i}(\pi_{M_i}) - f^{M_i}(\pi)$ and $D_i(\pi) = D^2_{\mathrm{H}}(M_i(\pi), \overline{M}(\pi))$ the two properties say that $\{M_1, \dots, M_N\}$ is an $(\alpha, \beta, \delta)$-family with respect to $\overline{M}$ (Definition 5.1), and the conclusion, holding for every $p$, gives $\mathsf{dec}_\gamma(\mathcal{M}', \overline{M}) \ge \alpha/2 - \gamma(\beta/N + \delta)$, which is (52). It is the template for every DEC lower bound in §§5–7 of the paper.
--
--   **Formalization Note** Definition 5.1 asks $u_i, v_i : \Pi \to [0,1]$; those range conditions are dropped, which makes the statement stronger, and is needed for Proposition 6.2, whose $u_i(\pi) = \pi_i$ can be negative. The proof on p. 32 uses only the two sum bounds. The nonnegativity of $\alpha$ and $\beta$ (scale parameters of the family) and the integrability of the four functions are stated explicitly. The conclusion exhibits a member attaining the bound, which is what the proof's averaging argument gives and implies the inequality between the inf over $p$ and the sup over the family.
-- source:
--   arXiv:2112.13487v3, Lemma 5.1, (52), p. 31 (proof p. 32); Definition 5.1, p. 31

import Mathlib

namespace StatComplexityDM.LinearLB

open MeasureTheory

/-- Lemma 5.1, (52) (arXiv:2112.13487v3, p. 31), for a general measurable decision space and an
arbitrary decision distribution `p`, without the range conditions `u_i, v_i ∈ [0, 1]` of
Definition 5.1: for an `(α, β, δ)`-family, some member `i` has
`E_{π∼p}[g_i(π) − γ D_i(π)] ≥ α/2 − γ(β/N + δ)`. -/
theorem hard_family_lower_bound_measure {X : Type*} [MeasurableSpace X]
    (p : ProbabilityMeasure X) (N : ℕ) (hN : 2 ≤ N) (α β δ γ : ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 < γ)
    (g D u v : Fin N → X → ℝ)
    (hg : ∀ i, Integrable (g i) (p : Measure X)) (hD : ∀ i, Integrable (D i) (p : Measure X))
    (hu : ∀ i, Integrable (u i) (p : Measure X)) (hv : ∀ i, Integrable (v i) (p : Measure X))
    (hreg : ∀ i x, α * (1 - u i x) ≤ g i x)
    (hinfo : ∀ i x, D i x ≤ β * v i x + δ)
    (hu_sum : ∀ x, ∑ i, u i x ≤ (N : ℝ) / 2)
    (hv_sum : ∀ x, ∑ i, v i x ≤ 1) :
    ∃ i : Fin N, α / 2 - γ * (β / N + δ) ≤ ∫ x, (g i x - γ * D i x) ∂(p : Measure X) := by sorry

end StatComplexityDM.LinearLB
