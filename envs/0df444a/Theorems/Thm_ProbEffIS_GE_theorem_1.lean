-- Prove2me | Theorems.Thm_ProbEffIS_GE_theorem_1
-- name    : ProbEffIS.GE.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:37.404002+00:00
-- url     : https://prove2.me/theorems/78d08913-80e9-4ac9-b0d5-df94ce9c532e
-- title:
--   Theorem 1, p. 8 — Gärtner–Ellis bounds, and the limit for a rare set with a dominating set (corrected)
-- statement:
--   Let $X_\gamma$ have laws $\nu_\gamma$ satisfying Assumption 1, let $I$ be the rate function, and let $B\subseteq\mathbb R^d$ be Borel. Then
--
--   $$
--   -I(B^\circ)\le\liminf_{\gamma\to\infty}\frac1\gamma\log\Pr(\gamma^{-1}X_\gamma\in B)\le\limsup_{\gamma\to\infty}\frac1\gamma\log\Pr(\gamma^{-1}X_\gamma\in B)\le-I(\overline B).
--   $$
--
--   If, in addition, $B$ satisfies Assumption 2 and admits a finite dominating set $\{a_1,\dots,a_r\}$ in the sense of Definition 2, then
--
--   $$
--   \lim_{\gamma\to\infty}\frac1\gamma\log\Pr(\gamma^{-1}X_\gamma\in B)=-I(B).
--   $$
--
--   The two bounds are the Gärtner–Ellis theorem, which the paper cites from Dembo and Zeitouni (2009) rather than proving. They supply the exponential decay rate of every rare-event probability used later.
--
--   **Formalization Note** The paper states the limit under Assumption 2 alone. That is not enough: for $X_\gamma=N_\gamma+U$ with $N_\gamma$ Poisson of mean $\gamma$ and $U$ uniform on $[0,1]$, independent, and $B=[-1,0]\cup[5,6]$, Assumptions 1 and 2 hold and $I(B)=I(0)=1$, but $X_\gamma>0$ almost surely, so the limit is $-I(5)=-(5\log5-4)$. The limit clause therefore also assumes a finite dominating set for $B$, which is the situation of every later use in the paper (Theorems 2, 5 and 6). The laws need only be probability measures for all sufficiently large $\gamma$, which is equivalent for this asymptotic claim.
-- source:
--   Bai, Huang, Lam & Zhao, Over-Conservativeness of Variance-Based Efficiency Criteria and Probabilistic Efficiency in Rare-Event Simulation, arXiv:2110.12573v2, p. 8, Theorem 1

import Mathlib
import Definitions.Def_ProbEffIS_GE_Defs

open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace

namespace ProbEffIS.GE

/-- Theorem 1, p. 8: the Gärtner–Ellis bounds, and the limit for a regular rare set.
    Correction: the printed limit clause assumes only Assumption 2, which does not suffice
    (counterexample: `X γ = Poisson(γ) + Uniform[0,1]`, `B = [-1,0] ∪ [5,6]`, where
    `I(B) = I(0) = 1` but the limit is `-I(5)`). The limit is stated under Assumption 2 together
    with the existence of a finite dominating set for `B` (Definition 2), which holds wherever the
    paper applies it. -/
theorem theorem_1 {d : ℕ} (ν : ℝ → Measure (Rd d))
    (hν : ∀ᶠ γ in atTop, IsProbabilityMeasure (ν γ))
    (μ : Rd d → EReal) (h1 : Assumption1 ν μ)
    (B : Set (Rd d)) (hB : MeasurableSet B) :
    -(rateOn μ (interior B)) ≤
      liminf (fun γ : ℝ => ((γ⁻¹ : ℝ) : EReal) *
        ENNReal.log (ν γ {x | γ⁻¹ • x ∈ B})) atTop ∧
    limsup (fun γ : ℝ => ((γ⁻¹ : ℝ) : EReal) *
      ENNReal.log (ν γ {x | γ⁻¹ • x ∈ B})) atTop ≤
        -(rateOn μ (closure B)) ∧
    (Assumption2 μ B → ∀ (r : ℕ) (a s : Fin r → Rd d), IsDominatingSet μ B a s →
      Tendsto (fun γ : ℝ => ((γ⁻¹ : ℝ) : EReal) *
        ENNReal.log (ν γ {x | γ⁻¹ • x ∈ B}))
        atTop (𝓝 (-(rateOn μ B)))) := by sorry

end ProbEffIS.GE
