-- Prove2me | Theorems.Thm_ParetoDDO_section_2_3_induced_pair
-- name    : ParetoDDO.section_2_3_induced_pair
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:35:02.745878+00:00
-- url     : https://prove2.me/theorems/8f05ce9b-5242-40ac-b277-a320e291d7ab
-- title:
--   §2.3 — a compressed pair induces a data-driven pair (corrected: $\tilde c(x,\cdot)$, $\tilde x$ Borel)
-- statement:
--   Assume Assumptions 2.1 and 2.2 and let $\widehat S$ be a statistic with state space $\mathbb S$ and $\mathbb S_\infty=S_\infty(\Theta)$. Let $(\tilde c,\tilde x)\in\tilde{\mathcal X}$ be a compressed data-driven predictor-prescriptor pair such that $s\mapsto\tilde c(x,s)$ ($x\in X$) and $\tilde x$ are Borel measurable on $\mathbb S$, and define
--   $$
--   \widehat c_T(x)=\tilde c(x,\widehat S_T),\qquad \widehat x_T=\tilde x(\widehat S_T).
--   $$
--   Then
--
--   1. $(\widehat c,\widehat x)\in\widehat{\mathcal X}$: $\widehat c$ is a data-driven predictor, $\widehat x$ is a data-driven prescriptor, and $\widehat c$ induces $\widehat x$;
--   2. $\widehat c_T(x)\to\tilde c(x,S_\infty(\theta))$ in $\mathbb P_\theta$-probability for all $x\in X$ and $\theta\in\Theta$;
--   3. $\min_{x\in X}\widehat c_T(x)\to\min_{x\in X}\tilde c(x,S_\infty(\theta))$ in $\mathbb P_\theta$-probability for all $\theta\in\Theta$.
--
--   This is the bridge from the restricted problem (2.6b) to the original problem (2.4b).
--
--   Differences from the source:
--   - correction: any compressed pair induces a data-driven pair satisfying Definitions 2.2–2.3 → the claim for compressed pairs with $\tilde c(x,\cdot)$ and $\tilde x$ Borel on $\mathbb S$; reason: counterexample satisfying every assumption of the source: in the Gaussian-mean model with $\Theta=(-1,1)$, $\widehat S_T$ the sample mean and $X=[0,1]$, $\tilde c(x,s)=\mathbf 1_N(s)$ with $N\subseteq[2,3]$ not Lebesgue measurable is bounded, continuous in $x$ and jointly continuous on $X\times\mathbb S_\infty$ (it vanishes there), but $\widehat c_1(x)=\mathbf 1_N(\xi_1)$ is not $\mathcal F_1$-measurable; $\tilde x=\mathbf 1_N$ (induced by $\tilde c\equiv0$) fails in the same way
--   - encoding: time $T\in\mathbb N=\{1,2,\dots\}$ → `T : ℕ` with every condition imposed for $1\le T$; the $T=0$ slice is unconstrained; reason: Lean's ℕ contains 0; limits ignore one term, so the objects are the same
--   - encoding: $X\subseteq\mathbb R^n$ compact, with $\min_{x\in X}$ used throughout → $X$ compact and nonempty; reason: the paper's minima over $X$ presuppose $X\neq\emptyset$; for empty $X$ the source's objects are undefined
--   - encoding: Assumption 2.2 on $X\times\Theta$, and $c$ also denotes its unique extension to $X\times\operatorname{cl}\Theta$ (p.12) → `c` is bounded and uniformly continuous on $X\times\operatorname{cl}\Theta$; reason: equivalent: the extension is unique and stays bounded and uniformly continuous, and the paper uses the extension
--   - encoding: $\mathbb P_\star\in\mathcal P$ (Assumption 2.1) → $\Theta\neq\emptyset$; $\mathbb P_\star$ is not represented; reason: $\mathbb P_\star$ enters no statement of the mission; its existence only gives $\Theta\neq\emptyset$
--   - encoding: $\mathbb P_\theta[\widehat S_T\in\mathbb S]=1$ (p.16) → $\widehat S_T(\omega)\in\mathbb S$ for every $\omega$ and $T\ge1$; reason: changing $\widehat S_T$ on an $\mathcal F_T$-set that is null for every $\theta$ changes no probability or expectation, and $\tilde c$, $\tilde x$ are only defined on $\mathbb S$
--   - encoding: the standing statistic $\widehat S$ of §2.3–§4 with state space $\mathbb S$ and $S_\infty$ → `IsStatistic ξ P Θ Ŝ S Sinf` as a hypothesis; reason: the result is stated in the paper's standing setting, where $\widehat S$ is a statistic (Definition 2.5)
-- source:
--   Sutter, Van Parys, Kuhn, A Pareto dominance principle for data-driven optimization, arXiv:2010.06606v4, §2.3, discussion after Definition 2.6, pp.17–18

import Mathlib
import Definitions.Def_ParetoDDO_Setting
import Definitions.Def_ParetoDDO_DataDriven
import Definitions.Def_ParetoDDO_Statistic

open MeasureTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace ParetoDDO

/-- **§2.3, discussion after Definition 2.6** (Sutter, Van Parys, Kuhn, arXiv:2010.06606v4, pp.17–18), corrected.
A compressed data-driven predictor-prescriptor pair `(c̃, x̃) ∈ X̃` and the statistic `Ŝ` induce
`ĉ_T(x) = c̃(x, Ŝ_T)` and `x̂_T = x̃(Ŝ_T)`. If `c̃(x, ·)` (for each `x ∈ X`) and `x̃` are Borel
measurable on `S`, then `(ĉ, x̂) ∈ X̂` with `x̂` induced by `ĉ`, `ĉ_T(x) → c̃(x, S∞(θ))` and
`min_x ĉ_T(x) → min_x c̃(x, S∞(θ))` in `P_θ`-probability for all `x ∈ X`, `θ ∈ Θ`.

**Formalization Note** The Borel hypotheses correct the source, which claims the induced pair is
adapted without them (counterexample in the item's description). -/
theorem section_2_3_induced_pair
    {Ω : Type*} [MeasurableSpace Ω] {m n d : ℕ}
    (ξ : ℕ → Ω → Vec m) (hξ : ∀ t, Measurable (ξ t))
    (P : Vec d → Measure Ω) (Θ : Set (Vec d)) (hP : IsAmbiguitySet P Θ)
    (X : Set (Vec n)) (hX : IsCompact X) (hXne : X.Nonempty)
    (c : Vec n → Vec d → ℝ) (hc : IsModelPredictor X Θ c)
    (Ŝ : ℕ → Ω → Vec d) (S : Set (Vec d)) (Sinf : Vec d → Vec d)
    (hS : IsStatistic ξ P Θ Ŝ S Sinf)
    (ct : Vec n → Vec d → ℝ) (xt : Vec d → Vec n) (hpair : IsCompressedPair X S Sinf Θ ct xt)
    (hct_meas : ∀ x ∈ X, Measurable (S.domRestrict (fun s => ct x s)))
    (hxt_meas : Measurable (S.domRestrict xt)) :
    IsPredictorPrescriptorPair ξ P Θ X (inducedPredictor ct Ŝ) (inducedPrescriptor xt Ŝ) ∧
      (∀ x ∈ X, ∀ θ ∈ Θ, TendstoInMeasure (P θ) (fun T => inducedPredictor ct Ŝ T x) atTop
        (fun _ => ct x (Sinf θ))) ∧
      (∀ θ ∈ Θ, TendstoInMeasure (P θ)
        (fun T ω => sInf ((fun x => inducedPredictor ct Ŝ T x ω) '' X)) atTop
        (fun _ => sInf ((fun x => ct x (Sinf θ)) '' X))) := by sorry

end ParetoDDO
