-- Prove2me | Theorems.Thm_PolarizedLearning_consumptionRate_converges
-- name    : PolarizedLearning.consumptionRate_converges
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:18:46.405208+00:00
-- url     : https://prove2.me/theorems/9baee80a-1732-4df3-8715-8aeb1621afba
-- title:
--   (EC.3) and (A1.1)–(A1.5), pp. ec1–ec2 — the consumption rate converges a.s. to a fixed point of the mean consumption map
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space with a filtration $(\mathcal F_t)_{t\ge0}$, and let $v_1,v_2,\dots$ be $\{0,1\}$-valued with $v_t$ $\mathcal F_t$-measurable (consumer $t$ consumes iff $v_t=1$). Let $n_t=\sum_{s=1}^{t-1}v_s$ be the view count seen by consumer $t$. Let $k:\mathbb R\to\mathbb R$ be continuous on $[0,1]$ and suppose that for every $t\ge2$,
--   $$\mathbb E[v_t\mid\mathcal F_{t-1}]=k\!\left(\frac{n_t}{t}\right)\quad\text{almost surely.}$$
--   Then almost surely there is $x_\infty\in[0,1]$ with $k(x_\infty)=x_\infty$ such that
--   $$x_t=\frac{n_t}{t-1}\longrightarrow x_\infty\quad\text{and}\quad\frac{n_t}{t}\longrightarrow x_\infty\qquad(t\to\infty).$$
--
--   In the model, $k(x)=L+(H-L)\int f(\pi,q)\,d\Psi(x)(\pi)+p(2u-1)$ is the mean consumption probability (EC.4), and the fixed point property is the paper's $h(x^*,q)=0$ at a limit point. The statement is the one-dimensional stochastic-approximation step behind both Theorems 1 and 2.
--
--   **Formalization Note** For $t\le1$ the quotients use Lean's convention $a/0=0$; only limits are asserted.
--
--   Differences from the source:
--   - generalization: the model's drift h(x,q) of (EC.4), continuous by (A1.3) → any k continuous on [0,1]; reason: specializes to k = mean consumption map, which is continuous under the goal's hypothesis
--   - generalization: the consumption process built from signals, group memberships, outside options and beliefs; conditioning on x_s, s < t → any {0,1}-valued process adapted to a filtration with the stated one-step conditional law for t ≥ 2 (v_1 unconstrained); reason: the primitive model induces this law with its natural filtration (paper.md item 7)
--   - reading: 'the process {x_t} converges with probability one' and 'h(x*(H),H) = 0 by definition of a stable limit point' → a.s. ∃ x∞ ∈ [0,1], k(x∞) = x∞, x_t → x∞ and n_t/t → x∞; reason: the paper's conclusion together with the fixed-point property it uses; the limit may depend on ω
--   - reading: law of v_t given the past in terms of x_t (EC.4), ML statistic n_t/t in (4)–(5) → conditional law at n_t/t; conclusion for x_t = n_t/(t−1) and n_t/t; reason: Π and Ψ are functions of n_t/t (p. ec1); the two quotients have the same limit (paper.md item 5)
-- source:
--   Kadiyala–Shin, Social Learning and Content Quality under Polarization, MSOM (2024), doi:10.1287/msom.2022.0533, e-companion, (EC.3), (A1.1)–(A1.5), p. ec1 (PDF 33); proof of Theorem 2, first paragraph, p. ec2 (PDF 34)

import Mathlib
import Definitions.Def_PolarizedLearning_Model

open MeasureTheory Filter Topology

namespace PolarizedLearning

/-- **The consumption rate converges almost surely to a fixed point of the mean consumption map**,
Kadiyala–Shin, *Social Learning and Content Quality under Polarization*, MSOM (2024),
doi:10.1287/msom.2022.0533, e-companion, (EC.3) and conditions (A1.1)–(A1.5), p. ec1 (PDF 33), and
proof of Theorem 2, p. ec2 (PDF 34): "These conditions imply that the process
`{x_t : t ≥ 1}` converges with probability one", with `h(x*, q) = 0` at the limit.

Let `v_1, v_2, …` be `{0,1}`-valued and adapted to a filtration `(ℱ_t)`, let
`n_t = Σ_{s=1}^{t−1} v_s`, and let `k` be continuous on `[0,1]` with
`E[v_t | ℱ_{t−1}] = k(n_t / t)` almost surely for every `t ≥ 2`. Then almost surely there is
`x_∞ ∈ [0,1]` with `k(x_∞) = x_∞` such that the consumption rate `x_t = n_t/(t − 1)` and
`n_t / t` both converge to `x_∞`.

**Formalization Note.** The paper applies Kushner–Yin (2003), Ch. 5, Thm 2.1 to the model's own
drift `h(x, q) = k(x) − x` of (EC.4); here `k` is any function continuous on `[0,1]`. The
conditional law is stated at `n_t / t`, the statistic of (4)–(5), so no bias term `β_t` appears.
For `t ≤ 1` the quotients use Lean's `a / 0 = 0`; only the limit is asserted. -/
theorem consumptionRate_converges {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ) (v : ℕ → Ω → ℝ)
    (hv01 : ∀ t ω, v t ω = 0 ∨ v t ω = 1) (hadapt : Adapted ℱ v)
    (k : ℝ → ℝ) (hk : ContinuousOn k (Set.Icc 0 1))
    (hlaw : ∀ t : ℕ, 2 ≤ t →
      μ[v t | ℱ (t - 1)] =ᵐ[μ] fun ω => k (viewCount v t ω / (t : ℝ))) :
    ∀ᵐ ω ∂μ, ∃ xInf ∈ Set.Icc (0 : ℝ) 1, k xInf = xInf ∧
      Tendsto (fun t : ℕ => viewCount v t ω / ((t : ℝ) - 1)) atTop (𝓝 xInf) ∧
      Tendsto (fun t : ℕ => viewCount v t ω / (t : ℝ)) atTop (𝓝 xInf) := by sorry

end PolarizedLearning
