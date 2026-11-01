-- Prove2me | Theorems.Thm_ParetoDDO_proposition_3_1
-- name    : ParetoDDO.proposition_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:34:59.774892+00:00
-- url     : https://prove2.me/theorems/f0b81ab4-89b2-4359-b4bb-19bc57e6c618
-- title:
--   Proposition 3.1 — continuity of the distributionally robust predictor $\tilde c^\star$
-- statement:
--   Assume Assumptions 2.1 and 2.2, let $\widehat S$ be a statistic with closed state space $\mathbb S$ and $\mathbb S_\infty=S_\infty(\Theta)$, assume Assumption 3.1 ($\widehat S$ satisfies an LDP with the regular rate function $I$, Definitions 3.2–3.3; imposed throughout §3.2, p.21) and let $r>0$. Then the distributionally robust predictor $\tilde c^\star$ of (3.3) is
--
--   1. bounded on $X\times\mathbb S$,
--   2. continuous in $x$ on $X\times\mathbb S$, and
--   3. continuous in $(x,s)$ on $X\times\mathbb S_\infty$;
--
--   that is, $\tilde c^\star$ is a compressed data-driven predictor (Definition 2.6).
--
--   This is the first step of the feasibility of $(\tilde c^\star,\tilde x^\star)$ and of $(\widehat c^\star,\widehat x^\star)$.
--
--   Differences from the source:
--   - encoding: time $T\in\mathbb N=\{1,2,\dots\}$ → `T : ℕ` with every condition imposed for $1\le T$; the $T=0$ slice is unconstrained; reason: Lean's ℕ contains 0; limits ignore one term, so the objects are the same
--   - encoding: $X\subseteq\mathbb R^n$ compact, with $\min_{x\in X}$ used throughout → $X$ compact and nonempty; reason: the paper's minima over $X$ presuppose $X\neq\emptyset$; for empty $X$ the source's objects are undefined
--   - encoding: Assumption 2.2 on $X\times\Theta$, and $c$ also denotes its unique extension to $X\times\operatorname{cl}\Theta$ (p.12) → `c` is bounded and uniformly continuous on $X\times\operatorname{cl}\Theta$; reason: equivalent: the extension is unique and stays bounded and uniformly continuous, and the paper uses the extension
--   - encoding: $\mathbb P_\star\in\mathcal P$ (Assumption 2.1) → $\Theta\neq\emptyset$; $\mathbb P_\star$ is not represented; reason: $\mathbb P_\star$ enters no statement of the mission; its existence only gives $\Theta\neq\emptyset$
--   - encoding: $\mathbb P_\theta[\widehat S_T\in\mathbb S]=1$ (p.16) → $\widehat S_T(\omega)\in\mathbb S$ for every $\omega$ and $T\ge1$; reason: changing $\widehat S_T$ on an $\mathcal F_T$-set that is null for every $\theta$ changes no probability or expectation, and $\tilde c$, $\tilde x$ are only defined on $\mathbb S$
--   - encoding: the standing statistic $\widehat S$ of §2.3–§4 with state space $\mathbb S$ and $S_\infty$ → `IsStatistic ξ P Θ Ŝ S Sinf` as a hypothesis; reason: the result is stated in the paper's standing setting, where $\widehat S$ is a statistic (Definition 2.5)
--   - encoding: $I:\mathbb S\times\operatorname{cl}\Theta\to[0,\infty]$ → `I : ℝ^d → ℝ^d → ℝ≥0∞`, only its values on $\mathbb S\times\operatorname{cl}\Theta$ are used; reason: Lean functions are total; the definitions read $I$ only on $\mathbb S\times\operatorname{cl}\Theta$
--   - encoding: $\max_{\theta\in\operatorname{cl}\Theta}\{c(x,\theta):I(s,\theta)\le r\}$ in (3.3) → `sSup` of the image of the feasible set; reason: the maximum is attained (p.21), so it equals the supremum
-- source:
--   Sutter, Van Parys, Kuhn, A Pareto dominance principle for data-driven optimization, arXiv:2010.06606v4, Proposition 3.1, p.21

import Mathlib
import Definitions.Def_ParetoDDO_Setting
import Definitions.Def_ParetoDDO_Statistic
import Definitions.Def_ParetoDDO_RateFunction
import Definitions.Def_ParetoDDO_DRPredictor

open MeasureTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace ParetoDDO

/-- **Proposition 3.1** (continuity of `c̃⋆`; Sutter, Van Parys, Kuhn, arXiv:2010.06606v4, p.21). Under
Assumptions 2.1 and 2.2 and the standing Assumption 3.1 of §3.2 (`Ŝ` satisfies an LDP with the
regular rate function `I`, imposed "throughout the rest of this section", p.21), if `r > 0`, then the distributionally
robust predictor `c̃⋆(x, s)` of (3.3) is bounded and continuous in `x` on `X × S` and continuous in
`(x, s)` on `X × S∞`, i.e. it is a compressed data-driven predictor (Definition 2.6). -/
theorem proposition_3_1
    {Ω : Type*} [MeasurableSpace Ω] {m n d : ℕ}
    (ξ : ℕ → Ω → Vec m) (hξ : ∀ t, Measurable (ξ t))
    (P : Vec d → Measure Ω) (Θ : Set (Vec d)) (hP : IsAmbiguitySet P Θ)
    (X : Set (Vec n)) (hX : IsCompact X) (hXne : X.Nonempty)
    (c : Vec n → Vec d → ℝ) (hc : IsModelPredictor X Θ c)
    (Ŝ : ℕ → Ω → Vec d) (S : Set (Vec d)) (Sinf : Vec d → Vec d)
    (hS : IsStatistic ξ P Θ Ŝ S Sinf)
    (I : Vec d → Vec d → ℝ≥0∞) (hLDP : IsLDP P Θ Ŝ S I)
    (hIreg : IsRegularRateFunction S Θ Sinf I)
    (r : ℝ) (hr : 0 < r) :
    IsCompressedPredictor X S Sinf Θ (drPredictor c Θ I r) := by sorry

end ParetoDDO
