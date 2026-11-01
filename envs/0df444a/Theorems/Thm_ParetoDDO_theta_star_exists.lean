-- Prove2me | Theorems.Thm_ParetoDDO_theta_star_exists
-- name    : ParetoDDO.theta_star_exists
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:35:28.948732+00:00
-- url     : https://prove2.me/theorems/75efd14c-796a-4e5d-a862-83d909159342
-- title:
--   Proof of Theorem 4.3, p.46 — a model $\theta^\star_0$ inside the $I$-ball nearly attains $\tilde c^\star$
-- statement:
--   Assume Assumptions 2.1, 2.2 and 3.1 (the statistic $\widehat S$ satisfies an LDP with a regular rate function $I$) and $r>0$. Let $\theta_0\in\Theta$, $x_0\in X$, $\varepsilon>0$ and $s_0=S_\infty(\theta_0)$. Then there is $\theta^\star_0\in\Theta$ with
--   $$
--   I(s_0,\theta^\star_0)<r\qquad\text{and}\qquad\tilde c^\star(x_0,s_0)<c(x_0,\theta^\star_0)+\varepsilon .
--   $$
--
--   This is the opening of Step 2 of the proof of Theorem 3.1, (D.2)–(D.4), reused in the proof of Theorem 4.3 to choose the model toward which a competitor is tilted.
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
--   - encoding: $\frac1T\log\mathbb P_\theta[\cdot]$ → `ENNReal.log` into $[-\infty,\infty]$, so $\log 0=-\infty$; reason: the source's convention; a real logarithm would send $\log 0$ to $0$
--   - reading: $\operatorname{int}\mathcal D$, $\operatorname{cl}\mathcal D$ in (3.1) → interior and closure relative to $\mathbb S$ (`relInterior S D`, `closure D ∩ S`); reason: §3.1 works in the subspace topology of $\mathbb S$ (p.19); for the closed set $\mathbb S$ the relative closure is the closure
--   - reading: "there exists $\theta^\star_0\in\Theta$ with $I(s_0,\theta^\star_0)=r_0<r$", in the setting of Theorem 4.3 → $I(s_0,\theta^\star_0)<r$ under the LDP with a regular $I$ (Assumption 3.1) as hypothesis; reason: $r_0$ is defined as $I(s_0,\theta^\star_0)$; the reused reasoning (p.41) needs exactly Assumption 3.1, which Theorem 4.3's proof obtains from Gärtner–Ellis
-- source:
--   Sutter, Van Parys, Kuhn, A Pareto dominance principle for data-driven optimization, arXiv:2010.06606v4, proof of Theorem 4.3, p.46 (reusing (D.2)–(D.4), proof of Theorem 3.1, p.41)

import Mathlib
import Definitions.Def_ParetoDDO_Setting
import Definitions.Def_ParetoDDO_Statistic
import Definitions.Def_ParetoDDO_RateFunction
import Definitions.Def_ParetoDDO_DRPredictor

open MeasureTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace ParetoDDO

/-- **The model `θ⋆₀` in the proof of Theorem 4.3** (Sutter, Van Parys, Kuhn, arXiv:2010.06606v4, p.46, reusing the
beginning of Step 2 of the proof of Theorem 3.1, (D.2)–(D.4), p.41). Under Assumptions 2.1, 2.2 and
3.1 and `r > 0`: for every `θ₀ ∈ Θ`, `x₀ ∈ X` and `ε > 0`, with `s₀ = S∞(θ₀)`, there is `θ⋆₀ ∈ Θ`
with `I(s₀, θ⋆₀) < r` and `c̃⋆(x₀, s₀) < c(x₀, θ⋆₀) + ε`. -/
theorem theta_star_exists
    {Ω : Type*} [MeasurableSpace Ω] {m n d : ℕ}
    (ξ : ℕ → Ω → Vec m) (hξ : ∀ t, Measurable (ξ t))
    (P : Vec d → Measure Ω) (Θ : Set (Vec d)) (hP : IsAmbiguitySet P Θ)
    (X : Set (Vec n)) (hX : IsCompact X) (hXne : X.Nonempty)
    (c : Vec n → Vec d → ℝ) (hc : IsModelPredictor X Θ c)
    (Ŝ : ℕ → Ω → Vec d) (S : Set (Vec d)) (Sinf : Vec d → Vec d)
    (hS : IsStatistic ξ P Θ Ŝ S Sinf)
    (I : Vec d → Vec d → ℝ≥0∞) (hLDP : IsLDP P Θ Ŝ S I)
    (hIreg : IsRegularRateFunction S Θ Sinf I)
    (r : ℝ) (hr : 0 < r)
    (θ₀ : Vec d) (hθ₀ : θ₀ ∈ Θ) (x₀ : Vec n) (hx₀ : x₀ ∈ X) (ε : ℝ) (hε : 0 < ε) :
    ∃ θ' ∈ Θ, I (Sinf θ₀) θ' < ENNReal.ofReal r ∧
      drPredictor c Θ I r x₀ (Sinf θ₀) < c x₀ θ' + ε := by sorry

end ParetoDDO
