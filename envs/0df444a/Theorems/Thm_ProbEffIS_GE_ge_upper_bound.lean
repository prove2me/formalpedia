-- Prove2me | Theorems.Thm_ProbEffIS_GE_ge_upper_bound
-- name    : ProbEffIS.GE.ge_upper_bound
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-02T02:19:03.895383+00:00
-- url     : https://prove2.me/theorems/a8c3e887-2cc2-412b-a02a-3eaa6f1e6e06
-- title:
--   Theorem 1 (upper bound) — Gärtner–Ellis large-deviation upper bound
-- statement:
--   Let $X_\gamma$ have laws $\nu_\gamma$ (probability measures for all large $\gamma$) whose scaled log-moment generating functions $\mu_\gamma(x)=\frac1\gamma\log E e^{x^\top X_\gamma}$ satisfy Assumption 1, with limit $\mu$ and rate function $I(y)=\sup_x\{x^\top y-\mu(x)\}$. Then for every Borel set $B\subseteq\mathbb R^d$
--
--   $$
--   \limsup_{\gamma\to\infty}\frac1\gamma\log\Pr(\gamma^{-1}X_\gamma\in B)\le-I(\overline B),\qquad I(\overline B)=\inf_{y\in\overline B}I(y).
--   $$
--
--   This is the upper-bound half of the Gärtner–Ellis theorem stated as Theorem 1 of the paper (cited there from Dembo and Zeitouni, Theorem 2.3.6(a)). Values are extended reals: $\log 0=-\infty$ and $I(\emptyset)=+\infty$.
-- source:
--   Bai, Huang, Lam & Zhao, Over-Conservativeness of Variance-Based Efficiency Criteria and Probabilistic Efficiency in Rare-Event Simulation, arXiv:2110.12573v2, p. 8, Theorem 1 (upper bound in the first display); Dembo & Zeitouni, Large Deviations Techniques and Applications, Theorem 2.3.6(a)

import Mathlib
import Definitions.Def_ProbEffIS_GE_Defs

open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace

namespace ProbEffIS.GE

/-- Theorem 1, p. 8 (upper bound): the Gärtner–Ellis large-deviation upper bound. -/
theorem ge_upper_bound {d : ℕ} (ν : ℝ → Measure (Rd d))
    (hν : ∀ᶠ γ in atTop, IsProbabilityMeasure (ν γ))
    (μ : Rd d → EReal) (h1 : Assumption1 ν μ)
    (B : Set (Rd d)) (hB : MeasurableSet B) :
    limsup (fun γ : ℝ => ((γ⁻¹ : ℝ) : EReal) *
      ENNReal.log (ν γ {x | γ⁻¹ • x ∈ B})) atTop ≤
        -(rateOn μ (closure B)) := by sorry

end ProbEffIS.GE
