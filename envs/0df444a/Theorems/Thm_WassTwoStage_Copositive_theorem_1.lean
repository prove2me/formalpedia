-- Prove2me | Theorems.Thm_WassTwoStage_Copositive_theorem_1
-- name    : WassTwoStage.Copositive.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:56:23.265283+00:00
-- url     : https://prove2.me/theorems/df08e04a-aa24-4016-a184-c9f44b9aea4c
-- title:
--   Theorem 1 — worst-case expectation over the 2-Wasserstein ball as a moment problem (5) and its dual (6)
-- statement:
--   Assume the setting of §3: the support $\Xi = \{\xi\ge0 : S\xi\le t\}$ is non-empty, the problem has sufficiently expensive recourse, $I \ge 1$, every sample $\hat\xi_i$ lies in $\Xi$, and $\epsilon \ge 0$. Fix a first-stage decision $x$. Then the worst-case expectation over the 2-Wasserstein ball with Euclidean transport cost equals the value of the generalized moment problem
--   $$\mathcal Z(x) = \sup\Big\{\frac1I\sum_{i\in[I]}\int_\Xi Z(x,\xi)\,\mathbb P_i(d\xi) \ :\ \mathbb P_i\in\mathcal M^2(\Xi)\ \forall i\in[I],\ \ \frac1I\sum_{i\in[I]}\int_\Xi \|\xi-\hat\xi_i\|_2^2\,\mathbb P_i(d\xi) \le \epsilon^2\Big\}, \qquad (5)$$
--   where $\mathcal M^2(\Xi)$ is the set of probability distributions supported on $\Xi$ with finite second moment. Moreover, if $\epsilon > 0$,
--   $$\mathcal Z(x) = \inf_{\lambda\in\mathbb R_+}\ \epsilon^2\lambda + \frac1I\sum_{i\in[I]}\sup_{\xi\in\Xi}\Big[Z(x,\xi) - \lambda\|\xi-\hat\xi_i\|_2^2\Big]. \qquad (6)$$
--
--   The moment form (5) is the starting point of the proof of Theorem 3, and the dual (6) that of Theorem 2.
--
--   **Formalization Note** The paper states Theorem 1 for a general $r \ge 1$ and a continuous reference metric $d$; this is the instance $r = 2$, $d(\xi,\xi') = \|\xi-\xi'\|_2$, polyhedral $\Xi$, used in §3. Integrals of the extended-real recourse value use the platform's expectation convention ($+\infty$ if the positive part has infinite integral); the transport cost is a lower Lebesgue integral. Finite second moment is written as $\int \|\xi\|_2^2\, d\mathbb P_i < \infty$, equivalent to finiteness around any reference point. The hypotheses $I \ge 1$ and $\hat\xi_i \in \Xi$ are implicit in the paper (the samples are drawn from a distribution on $\Xi$).
-- source:
--   Hanasusanto, Kuhn, Conic Programming Reformulations of Two-Stage Distributionally Robust Linear Programs over Wasserstein Balls, arXiv:1609.07505v3, p. 7, Theorem 1, (5), (6); proof Appendix A, p. 38

import Mathlib
import Definitions.Def_WassTwoStage_Copositive_Setting

open MeasureTheory

namespace WassTwoStage.Copositive

/-- Theorem 1, Hanasusanto–Kuhn, arXiv:1609.07505v3, p. 7 (proof in Appendix A, p. 38), in the
setting of §3: `r = 2`, `d(ξ, ξ') = ‖ξ − ξ'‖₂`, `Ξ = {ξ ≥ 0 : Sξ ≤ t}`. The worst-case expectation
(2) equals the value of the generalized moment problem (5), a supremum over families
`(ℙ_i)_{i∈[I]}` of probability measures supported on `Ξ` with finite second moment, subject to
`(1/I) Σ_i ∫ ‖ξ − ξ̂_i‖² dℙ_i ≤ ε²`; and for `ε > 0` it equals the dual (6),
`inf_{λ ≥ 0} ε²λ + (1/I) Σ_i sup_{ξ∈Ξ} [Z(x, ξ) − λ‖ξ − ξ̂_i‖²]`. -/
theorem theorem_1 {K J M N₁ N₂ I : ℕ} (d : Data K J M N₁ N₂ I) (hI : 0 < I)
    (hXi : d.Xi.Nonempty) (hSER : d.SufficientlyExpensiveRecourse)
    (hξ : ∀ i, d.ξhat i ∈ d.Xi) (hε : 0 ≤ d.ε) (x : Fin N₁ → ℝ) :
    (d.worstCase x =
      ⨆ (P : Fin I → Measure (EuclideanSpace ℝ (Fin K)))
        (_ : (∀ i, IsProbabilityMeasure (P i) ∧ P i d.Xiᶜ = 0 ∧
              ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ 2) ∂(P i) < ⊤) ∧
            (I : ENNReal)⁻¹ * ∑ i, ∫⁻ ξ, ENNReal.ofReal (‖ξ - d.ξhat i‖ ^ 2) ∂(P i)
              ≤ ENNReal.ofReal (d.ε ^ 2)),
        (((I : ℝ)⁻¹ : ℝ) : EReal) *
          ∑ i, WassersteinDRO.Duality.erealExpectation (P i) (fun ξ => d.recourse x ξ)) ∧
    (0 < d.ε → d.worstCase x =
      ⨅ (lam : ℝ) (_ : 0 ≤ lam), ((d.ε ^ 2 * lam : ℝ) : EReal) +
        (((I : ℝ)⁻¹ : ℝ) : EReal) *
          ∑ i, ⨆ (ξ : EuclideanSpace ℝ (Fin K)) (_ : ξ ∈ d.Xi),
            (d.recourse x ξ - ((lam * ‖ξ - d.ξhat i‖ ^ 2 : ℝ) : EReal))) := by sorry

end WassTwoStage.Copositive
