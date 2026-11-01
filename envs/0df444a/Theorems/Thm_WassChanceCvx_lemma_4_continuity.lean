-- Prove2me | Theorems.Thm_WassChanceCvx_lemma_4_continuity
-- name    : WassChanceCvx.lemma_4_continuity
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:26:17.686059+00:00
-- url     : https://prove2.me/theorems/8ba7d3b7-b095-4274-b7aa-6f9d564d23ad
-- title:
--   Lemma 4 — $\psi(x,t)$ and $\phi(x,y)=\int_0^y\psi(x,t)\,dt$ are continuous on $\mathbb R^n\times\mathbb R_+$
-- statement:
--   Let $\mathbb P$ be an α-concave Borel probability measure on the finite-dimensional real normed space $E$, $\epsilon\in(0,1)$, and let $f:\mathbb R^n\times E\to\mathbb R$ be continuous with $f(x,\zeta)$ atomless for every $x$, i.e. $\mathbb P[f(x,\zeta)=y]=0$ for all $x\in\mathbb R^n$ and $y\in\mathbb R$. Then
--
--   $$
--   \psi(x,t):=\mathbb P[f(x,\zeta)\ge t]-(1-\epsilon)\qquad\text{and}\qquad \phi(x,y):=\int_0^y\psi(x,t)\,dt
--   $$
--
--   are both continuous on $\mathbb R^n\times[0,\infty)$.
--
--   The continuity of $\phi$, composed with the continuous quantile of Lemma 3, makes the right side of (5) continuous, hence its feasible region closed.
--
--   **Formalization Note** Continuity is `ContinuousOn` on $\mathbb R^n\times[0,\infty)$, for each of $\psi$ and $\phi$.
--
--   Differences from the source:
--   - encoding: ℝ^q (written ℝ^m in §3.1) with an arbitrary norm ‖·‖; rows $a_i$ with dual norm $\|a_i\|_*$ → a finite-dimensional real normed space $E$ with its Borel σ-algebra; rows are continuous linear functionals on $E$, $\|a_i\|_*$ their operator norm; reason: the same objects: ℝ^q with any norm is such a space and the dual norm is the operator norm
--   - reading: $\mathcal P_0$ is the set of all probability distributions; $\Xi$ is the support of $\xi$ → all Borel probability measures on $E$; $\Xi=E$; reason: p.3 takes all probability distributions, and the proof of Theorem 1 (p.8) uses $d(\zeta,\mathcal S^c(x))=(f(x,\zeta))^+$ for every $\zeta\in\mathbb R^m$, which holds only when the unsafe set is taken in all of $\mathbb R^m$
--   - encoding: Definition 2: $\mathbb P$ on the Lebesgue subsets of a convex $\Omega$, Borel $A,B\subseteq\Omega$, $\mathbb P(\theta A+(1-\theta)B)\ge m_\alpha(\mathbb P(A),\mathbb P(B);\theta)$ → `IsAlphaConcaveMeasure α P`: all measurable $A,B\subseteq E$, $P$ evaluated on $\theta A+(1-\theta)B$ as Mathlib's outer measure, values compared through `toReal`; reason: equivalent: $\theta A+(1-\theta)B$ is analytic, so its outer measure is its Lebesgue (completion) measure; $\Omega$ is immaterial because $m_\alpha$ is nondecreasing in each argument; probabilities are finite
--   - encoding: $\alpha\in\overline{\mathbb R}$ → `α : EReal`; reason: same values $[-\infty,+\infty]$
--   - encoding: $1-\epsilon\in(0,1)$, the standing assumption of p.1 → hypotheses `0 < ϵ` and `ϵ < 1`; reason: same range
--   - encoding: $f(x,\zeta)$ is atomless for any $x$ → $\mathbb P\{\zeta: f(x,\zeta)=y\}=0$ for all $x$ and all real $y$; reason: the definition of an atomless random variable
--   - encoding: $\mathbb R^n$; $\psi$; $\int_0^y$ → `Fin n → ℝ`; probabilities through `toReal`; the interval integral `∫ t in 0..y`; reason: the same objects; $y\ge0$ on the stated domain and probabilities are finite
-- source:
--   Shen, Jiang, Convex Chance-Constrained Programs with Wasserstein Ambiguity, arXiv:2111.02486v2, Lemma 4, p.8

import Mathlib
import Definitions.Def_WassChanceCvx_IsAlphaConcaveMeasure

open MeasureTheory

namespace WassChanceCvx

/-- **Lemma 4 (continuity of `ψ` and `ϕ`).**
Shen, Jiang, arXiv:2111.02486v2, Lemma 4, p.8: "Suppose that `f(·, ·) : ℝⁿ × Ξ → ℝ` is a continuous
function, `ζ` follows an α-concave distribution `ℙ`, and `f(x, ζ)` is atomless for any `x ∈ ℝⁿ`.
Then, `ψ(x, t) := ℙ[f(x, ζ) ≥ t] − (1 − ϵ)` and `ϕ(x, y) := ∫_0^y ψ(x, t) dt` are both continuous
on `ℝⁿ × ℝ₊`."

**Formalization Note.** `Ξ = E`; `f` is jointly continuous on `ℝⁿ × E`; "atomless" is
`P{ζ : f(x, ζ) = y} = 0` for all `x` and all real `y`. Both conclusions are `ContinuousOn` on
`ℝⁿ × [0, ∞)`. `ϕ(x, y)` is the interval integral `∫ t in 0..y`. `α` is any extended real and
`ϵ ∈ (0, 1)` is the standing assumption of p.1. -/
theorem lemma_4_continuity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {n : ℕ} (f : (Fin n → ℝ) → E → ℝ)
    (hf : Continuous (fun p : (Fin n → ℝ) × E => f p.1 p.2))
    (P : Measure E) [IsProbabilityMeasure P] (α : EReal) (hP : IsAlphaConcaveMeasure α P)
    (hatom : ∀ (x : Fin n → ℝ) (y : ℝ), P {ζ | f x ζ = y} = 0)
    (ϵ : ℝ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1) :
    ContinuousOn (fun p : (Fin n → ℝ) × ℝ => (P {ζ | p.2 ≤ f p.1 ζ}).toReal - (1 - ϵ))
        (Set.univ ×ˢ Set.Ici 0) ∧
      ContinuousOn (fun p : (Fin n → ℝ) × ℝ =>
          ∫ t in (0 : ℝ)..p.2, ((P {ζ | t ≤ f p.1 ζ}).toReal - (1 - ϵ)))
        (Set.univ ×ˢ Set.Ici 0) := by sorry

end WassChanceCvx
