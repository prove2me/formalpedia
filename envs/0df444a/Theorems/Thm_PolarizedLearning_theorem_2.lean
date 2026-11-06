-- Prove2me | Theorems.Thm_PolarizedLearning_theorem_2
-- name    : PolarizedLearning.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:18:50.012765+00:00
-- url     : https://prove2.me/theorems/2abb8273-c0db-46fb-b85a-d9e8a04c31f2
-- title:
--   Theorem 2 — with $p>0$, $\bar q_t\to\bar q_\infty$ a.s., $\bar q_\infty<H$ if $q=H$, $\bar q_\infty>L$ if $q=L$ (corrected: stationary belief kernel $\Psi(n_t/t)$ with continuous mean)
-- statement:
--   This is the incomplete-learning theorem: with polarized preferences, social learning from view counts converges but never reveals the true quality.
--
--   Fix parameters $H>L$, polarization $p>0$, in-group share $u\in(0,1)$, uncertainty $\epsilon>0$ with $[u-\epsilon,u+\epsilon]\subseteq[0,1]$, $L-p>0$, $H+p<1$, and signal accuracy $1/2<\alpha<1$. Fix the true quality $q\in\{H,L\}$ and a belief kernel $\Psi$: each $\Psi(x)$ is a probability measure on $\mathbb R$ with $\Psi(x)(\Pi(x))=1$ for $x\in[0,1]$, where $\Pi(x)=[\pi^-(x),\pi^+(x)]$ is the set of ML quality beliefs. Assume
--
--   1. (Assumption 1) $\Psi(x)\bigl((\pi^-(x),\pi^+(x))\bigr)>0$ whenever $\pi^-(x)<\pi^+(x)$;
--   2. $x\mapsto\int f(\pi,q)\,d\Psi(x)(\pi)$ is continuous on $[0,1]$, where $f$ is the expected posterior (3).
--
--   Let $v_1,v_2,\dots\in\{0,1\}$ be consumption decisions adapted to a filtration $(\mathcal F_t)$ on a probability space, with view counts $n_t=\sum_{s=1}^{t-1}v_s$, such that for every $t\ge2$
--   $$\mathbb P(v_t=1\mid\mathcal F_{t-1})=L+(H-L)\int f(\pi,q)\,d\Psi(n_t/t)(\pi)+p(2u-1)\quad\text{a.s.}$$
--   Write $\bar q_t=L+(H-L)\int f(\pi,q)\,d\Psi(n_t/t)(\pi)$ for the average quality estimate of consumer $t$. Then there is a random variable $\bar q_\infty$ such that, almost surely,
--   $$\bar q_t\longrightarrow\bar q_\infty\quad(t\to\infty),\qquad \bar q_\infty<H\ \text{ if } q=H,\qquad \bar q_\infty>L\ \text{ if } q=L.$$
--
--   Without polarization the same mechanism reveals the quality (Theorem 1); with it, high-quality content is underestimated and low-quality content overestimated forever.
--
--   **Formalization Note** The process enters only through its one-step conditional law, which the primitive model induces. For $t\le1$ the quotient $n_t/t$ uses Lean's $a/0=0$; only the limit is asserted.
--
--   Differences from the source:
--   - correction: Ψ_t ∈ ∆(Π_t) arbitrary for each t → one kernel Ψ evaluated at n_t/t, with x ↦ ∫ f(·,q) dΨ(x) continuous on [0,1] ((EC.4), (A1.3)); reason: with Ψ_t the Dirac at π⁻_t + θ_t(π⁺_t − π⁻_t), θ_t = 0.99 for even t and 0.01 for odd t, every assumption holds and q̄_t oscillates (paper.md item 2)
--   - reading: Assumption 1: P_Ψt(π_t ∈ (π−t, π+t)) > 0 for t ≥ 2 → required only where π⁻(x) < π⁺(x); reason: literally unsatisfiable on {v_1 = … = v_{t−1} = 1}, where Π_t = {1} (paper.md item 1)
--   - reading: α > 0.5; ϵ a degree of uncertainty → 1/2 < α < 1 and ϵ > 0; reason: at α = 1 learning is complete (paper.md item 3); with ϵ = 0 Π is a singleton and learning is complete (item 4)
--   - reading: q̄t → q̄∞ almost surely, q̄∞ < H (q = H), q̄∞ > L (q = L) → ∃ Q∞ : Ω → ℝ, a.s. q̄_t → Q∞ and the bias clause holds for Q∞; reason: the limit point may depend on the path; the proof never shows it is deterministic (paper.md item 6)
--   - reading: Π_t and Ψ_t as functions of n_t and t → Π and Ψ evaluated at n_t/t; reason: (4) and (5) depend on n_t only through n_t/t, as the e-companion's ℓ̃(x; ·) makes explicit (paper.md item 5)
--   - generalization: the process built from σ_t, r_t, U^o_t and π_t ∼ Ψ_t → any {0,1}-valued process adapted to a filtration with the one-step law (EC.4) for t ≥ 2 (v_1, whose law the prior π_1 fixes, unconstrained); reason: the primitive model induces this law (paper.md item 7), so it is a special case
--   - generalization: continuity of h(·,q) from continuity of the belief rule (A1.3) → continuity of x ↦ ∫ f(π,q) dΨ(x)(π) on [0,1] only; reason: weaker hypothesis than weak continuity of Ψ; every weakly continuous kernel satisfies it
--   - encoding: Π_t = [π−t, π+t] with π±t = min/max, Ψt ∈ ∆(Πt) → Π(x) = Prod.fst '' argmax, π± = sInf/sSup, Ψ(x) a probability measure on ℝ with Ψ(x)(Π(x)) = 1; reason: same objects; Π(x) is a nonempty compact interval for x ∈ [0,1]
-- source:
--   Kadiyala–Shin, Social Learning and Content Quality under Polarization, MSOM (2024), doi:10.1287/msom.2022.0533, §4.1.2, Theorem 2, p. 14 (PDF 14), with Assumption 1, p. 14, and the model of §3.2–§3.4, pp. 8–14; e-companion, proof of Theorem 2, p. ec2 (PDF 34)

import Mathlib
import Definitions.Def_PolarizedLearning_Model

open MeasureTheory Filter Topology

namespace PolarizedLearning

/-- **Theorem 2 (incomplete learning under polarization)**, Kadiyala–Shin, *Social Learning and
Content Quality under Polarization*, MSOM (2024), doi:10.1287/msom.2022.0533, §4.1.2, p. 14
(PDF 14), with Assumption 1 (p. 14) and the model of §3.2–§3.4 (pp. 8–14).

Fix the parameters (`p > 0`, `ϵ > 0`, `1/2 < α < 1`), the true quality `q ∈ {H, L}`, and a belief
kernel `Ψ` carried by the ML beliefs `Π(x)`, satisfying Assumption 1 where `Π(x)` is not a singleton,
with `x ↦ ∫ f(π, q) dΨ(x)(π)` continuous on `[0,1]`. Let `v_1, v_2, …` be `{0,1}`-valued
consumption decisions adapted to `(ℱ_t)` whose conditional consumption probability given
`ℱ_{t−1}` is `L + (H − L) ∫ f(π, q) dΨ(n_t/t)(π) + p(2u − 1)` for `t ≥ 2` ((EC.4)). Then there is a
random variable `Q_∞` such that, almost surely, the average quality estimate
`q̄_t = L + (H − L) ∫ f(π, q) dΨ(n_t/t)(π)` converges to `Q_∞`, with `Q_∞ < H` if `q = H` and
`Q_∞ > L` if `q = L`.

**Formalization Note.** The process is given through its one-step conditional law, which the
primitive model (signals, group memberships, outside options and beliefs drawn afresh) induces.
For `t ≤ 1` the quotient `n_t / t` uses Lean's `a / 0 = 0`; only the limit is asserted. -/
theorem theorem_2 (P : Params) (q : Quality) (Ψ : ℝ → Measure ℝ)
    (hΨ : IsBeliefKernel P Ψ) (hA1 : Assumption1 P Ψ)
    (hcont : ContinuousOn (fun x => ∫ π, f P.al π q ∂(Ψ x)) (Set.Icc 0 1))
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) (v : ℕ → Ω → ℝ)
    (hv01 : ∀ t ω, v t ω = 0 ∨ v t ω = 1) (hadapt : Adapted ℱ v)
    (hlaw : ∀ t : ℕ, 2 ≤ t →
      μ[v t | ℱ (t - 1)] =ᵐ[μ] fun ω => meanConsumption P q Ψ (viewCount v t ω / (t : ℝ))) :
    ∃ QInf : Ω → ℝ, ∀ᵐ ω ∂μ,
      Tendsto (fun t : ℕ => avgQuality P q Ψ (viewCount v t ω / (t : ℝ))) atTop (𝓝 (QInf ω)) ∧
      (q = .high → QInf ω < P.H) ∧ (q = .low → P.L < QInf ω) := by sorry

end PolarizedLearning
