-- Prove2me | Theorems.Thm_ProbEffIS_GE_ge_lower_bound
-- name    : ProbEffIS.GE.ge_lower_bound
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-02T02:19:06.210598+00:00
-- url     : https://prove2.me/theorems/49a9b87b-ae43-4608-8c82-867d7b20ee0c
-- title:
--   Theorem 1 (lower bound) — Gärtner–Ellis large-deviation lower bound
-- statement:
--   Let $X_\gamma$ have laws $\nu_\gamma$ (probability measures for all large $\gamma$) whose scaled log-moment generating functions $\mu_\gamma(x)=\frac1\gamma\log E e^{x^\top X_\gamma}$ satisfy Assumption 1 (pointwise limit $\mu$ in $[-\infty,\infty]$, $0\in D(\mu)^\circ$, $\mu$ differentiable on $D(\mu)^\circ$ and steep), and let $I(y)=\sup_x\{x^\top y-\mu(x)\}$. Then for every Borel set $B\subseteq\mathbb R^d$
--
--   $$
--   -I(B^\circ)\le\liminf_{\gamma\to\infty}\frac1\gamma\log\Pr(\gamma^{-1}X_\gamma\in B),\qquad I(B^\circ)=\inf_{y\in B^\circ}I(y).
--   $$
--
--   This is the lower-bound half of the Gärtner–Ellis theorem stated as Theorem 1 of the paper (cited there from Dembo and Zeitouni, Theorem 2.3.6(b),(c)). Values are extended reals.
-- source:
--   Bai, Huang, Lam & Zhao, Over-Conservativeness of Variance-Based Efficiency Criteria and Probabilistic Efficiency in Rare-Event Simulation, arXiv:2110.12573v2, p. 8, Theorem 1 (lower bound in the first display); Dembo & Zeitouni, Large Deviations Techniques and Applications, Theorem 2.3.6(b),(c)

import Mathlib
import Definitions.Def_ProbEffIS_GE_Defs

open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace

namespace ProbEffIS.GE

/-- Theorem 1, p. 8 (lower bound): the Gärtner–Ellis large-deviation lower bound. -/
theorem ge_lower_bound {d : ℕ} (ν : ℝ → Measure (Rd d))
    (hν : ∀ᶠ γ in atTop, IsProbabilityMeasure (ν γ))
    (μ : Rd d → EReal) (h1 : Assumption1 ν μ)
    (B : Set (Rd d)) (hB : MeasurableSet B) :
    -(rateOn μ (interior B)) ≤
      liminf (fun γ : ℝ => ((γ⁻¹ : ℝ) : EReal) *
        ENNReal.log (ν γ {x | γ⁻¹ • x ∈ B})) atTop := by sorry

end ProbEffIS.GE
