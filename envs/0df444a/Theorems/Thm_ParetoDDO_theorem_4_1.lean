-- Prove2me | Theorems.Thm_ParetoDDO_theorem_4_1
-- name    : ParetoDDO.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:35:03.662475+00:00
-- url     : https://prove2.me/theorems/75e70516-214a-4109-aa62-1a7573b8889d
-- title:
--   Theorem 4.1 — Gärtner–Ellis: $\widehat S$ satisfies an LDP with the good rate function (4.4)
-- statement:
--   Let $\widehat S$ be a statistic with closed state space $\mathbb S$ under Assumption 2.1, and let the limiting log-moment generating function $\Lambda$ satisfy Assumption 4.2. Write
--   $$
--   I(s,\theta)=\sup_{\lambda\in\mathbb R^d}\ \langle\lambda,s\rangle-\Lambda(\lambda,\theta). \tag{4.4}
--   $$
--   Then
--
--   1. $I(s,\theta)\ge0$ for all $s$ and $\theta\in\Theta$;
--   2. $s\mapsto I(s,\theta)$ is lower semicontinuous on $\mathbb S$ for $\theta\in\Theta$;
--   3. $\widehat S$ satisfies the LDP (3.1) with rate function $I$ (Definition 3.2);
--   4. $I$ is good: $\{s\in\mathbb S:I(s,\theta)\le\rho\}$ is compact for all $\rho\ge0$, $\theta\in\Theta$.
--
--   This is the source of the LDP that drives the feasibility of the distributionally robust pair.
--
--   **Formalization Note** Because of item 1, the $[0,\infty]$-valued version of (4.4) used in items 2–4 (`EReal.toENNReal`) is (4.4) itself. No lower semicontinuity of $\Lambda$ is assumed, as in the paper's statement.
--
--   Differences from the source:
--   - encoding: time $T\in\mathbb N=\{1,2,\dots\}$ → `T : ℕ` with every condition imposed for $1\le T$; the $T=0$ slice is unconstrained; reason: Lean's ℕ contains 0; limits ignore one term, so the objects are the same
--   - encoding: $\mathbb P_\star\in\mathcal P$ (Assumption 2.1) → $\Theta\neq\emptyset$; $\mathbb P_\star$ is not represented; reason: $\mathbb P_\star$ enters no statement of the mission; its existence only gives $\Theta\neq\emptyset$
--   - encoding: $\mathbb P_\theta[\widehat S_T\in\mathbb S]=1$ (p.16) → $\widehat S_T(\omega)\in\mathbb S$ for every $\omega$ and $T\ge1$; reason: changing $\widehat S_T$ on an $\mathcal F_T$-set that is null for every $\theta$ changes no probability or expectation, and $\tilde c$, $\tilde x$ are only defined on $\mathbb S$
--   - encoding: the standing statistic $\widehat S$ of §2.3–§4 with state space $\mathbb S$ and $S_\infty$ → `IsStatistic ξ P Θ Ŝ S Sinf` as a hypothesis; reason: the result is stated in the paper's standing setting, where $\widehat S$ is a statistic (Definition 2.5)
--   - encoding: Assumption 4.2 defines $\Lambda$ as the limit (4.3) → a function `Λ` with `IsLogMGFRegular P Θ Ŝ Λ`, which states that (4.3) converges to it; reason: the limit is unique, so quantifying over such $\Lambda$ is the same as using the limit
--   - encoding: $\frac1T\log\mathbb P_\theta[\cdot]$ → `ENNReal.log` into $[-\infty,\infty]$, so $\log 0=-\infty$; reason: the source's convention; a real logarithm would send $\log 0$ to $0$
--   - reading: $\operatorname{int}\mathcal D$, $\operatorname{cl}\mathcal D$ in (3.1) → interior and closure relative to $\mathbb S$ (`relInterior S D`, `closure D ∩ S`); reason: §3.1 works in the subspace topology of $\mathbb S$ (p.19); for the closed set $\mathbb S$ the relative closure is the closure
--   - reading: "$\widehat S$ satisfies an LDP with good rate function (4.4)", with Definitions 3.1–3.2 on $\mathbb S\times\operatorname{cl}\Theta$ → the LDP and goodness for $\theta\in\Theta$, nonnegativity and lower semicontinuity in $s$ for $\theta\in\Theta$; reason: (4.4) is defined only on $\mathbb R^d\times\Theta$ (p.24), and Definition 3.2 quantifies over $\theta\in\Theta$ only
-- source:
--   Sutter, Van Parys, Kuhn, A Pareto dominance principle for data-driven optimization, arXiv:2010.06606v4, Theorem 4.1, (4.4), p.24 (citing Dembo–Zeitouni, Theorem 2.3.6)

import Mathlib
import Definitions.Def_ParetoDDO_Setting
import Definitions.Def_ParetoDDO_Statistic
import Definitions.Def_ParetoDDO_RateFunction
import Definitions.Def_ParetoDDO_ExpFamily

open MeasureTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace ParetoDDO

/-- **Theorem 4.1** (Gärtner–Ellis theorem; Sutter, Van Parys, Kuhn, arXiv:2010.06606v4, p.24, citing Dembo–Zeitouni,
Theorem 2.3.6). If the limiting log-moment generating function `Λ` satisfies Assumption 4.2, then the
statistic `Ŝ` satisfies an LDP (Definition 3.2) with the good rate function
`I(s, θ) = sup_λ ⟨λ, s⟩ − Λ(λ, θ)` of (4.4).

**Formalization Note** The conclusion has four parts: (4.4) is nonnegative for `θ ∈ Θ` (so its
`[0, ∞]`-valued version `toENNReal` is the same function), it is lower semicontinuous in `s` on `S`,
the LDP (3.1) holds with it, and it is good. -/
theorem theorem_4_1
    {Ω : Type*} [MeasurableSpace Ω] {m d : ℕ}
    (ξ : ℕ → Ω → Vec m) (hξ : ∀ t, Measurable (ξ t))
    (P : Vec d → Measure Ω) (Θ : Set (Vec d)) (hP : IsAmbiguitySet P Θ)
    (Ŝ : ℕ → Ω → Vec d) (S : Set (Vec d)) (Sinf : Vec d → Vec d)
    (hS : IsStatistic ξ P Θ Ŝ S Sinf)
    (Λ : Vec d → Vec d → EReal) (h42 : IsLogMGFRegular P Θ Ŝ Λ) :
    (∀ s : Vec d, ∀ θ ∈ Θ, 0 ≤ gartnerEllisRate Λ s θ) ∧
      (∀ θ ∈ Θ, LowerSemicontinuousOn (fun s => (gartnerEllisRate Λ s θ).toENNReal) S) ∧
      IsLDP P Θ Ŝ S (fun s θ => (gartnerEllisRate Λ s θ).toENNReal) ∧
      IsGoodRateFunction S Θ (fun s θ => (gartnerEllisRate Λ s θ).toENNReal) := by sorry

end ParetoDDO
