-- Prove2me | Theorems.Thm_WassChanceCvx_proposition_2
-- name    : WassChanceCvx.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:27:19.195848+00:00
-- url     : https://prove2.me/theorems/053364c0-bc78-4255-b157-f79a234da58e
-- title:
--   Proposition 2 — $\mathcal X^p$ as the constraints (5)–(6) for an α-concave reference
-- statement:
--   Let $\mathbb P$ be an α-concave Borel probability measure on the finite-dimensional real normed space $E$, $\delta>0$, $\epsilon\in(0,1)$, $A(x)$ and $b(x)$ affine in $x$, $\zeta\sim\mathbb P$, and $f$ the slack. Then for every $x$ with $A(x)\ne0$, $x\in\mathcal X^p$ if and only if
--
--   $$
--   \delta\le\int_0^{\mathrm{VaR}_\epsilon(f(x,\zeta))}\Bigl(\mathbb P[f(x,\zeta)\ge t]-(1-\epsilon)\Bigr)dt\quad(5)\qquad\text{and}\qquad \mathbb P[A(x)\zeta\le b(x)]\ge1-\epsilon\quad(6).
--   $$
--
--   Constraint (6) is the ordinary chance constraint under the reference distribution; constraint (5) measures the transport budget needed to violate it, which must exceed the radius $\delta$. This reformulation is the starting point of the proof of Theorem 1.
--
--   **Formalization Note** $\mathrm{VaR}_\epsilon$ is the lower $\epsilon$-quantile of the law of $f(x,\zeta)$. The integral is oriented: if $v=\mathrm{VaR}_\epsilon(f(x,\zeta))<0$ it equals $-\int_v^0$.
--
--   Differences from the source:
--   - encoding: ℝ^q (written ℝ^m in §3.1) with an arbitrary norm ‖·‖; rows $a_i$ with dual norm $\|a_i\|_*$ → a finite-dimensional real normed space $E$ with its Borel σ-algebra; rows are continuous linear functionals on $E$, $\|a_i\|_*$ their operator norm; reason: the same objects: ℝ^q with any norm is such a space and the dual norm is the operator norm
--   - encoding: decision $x\in\mathbb R^n$; $A(x)\in\mathbb R^{m\times q}$ and $b(x)\in\mathbb R^m$ affine in $x$ → `Fin n → ℝ`; `A` an affine map into $k$-tuples of functionals on $E$, `b` an affine map into $\mathbb R^k$; reason: same data; $k$ rows of $A(x)$, each a functional on $E$
--   - reading: $\mathcal P_0$ is the set of all probability distributions; $\Xi$ is the support of $\xi$ → all Borel probability measures on $E$; $\Xi=E$; reason: p.3 takes all probability distributions, and the proof of Theorem 1 (p.8) uses $d(\zeta,\mathcal S^c(x))=(f(x,\zeta))^+$ for every $\zeta\in\mathbb R^m$, which holds only when the unsafe set is taken in all of $\mathbb R^m$
--   - encoding: $\inf_{\mathbb Q\in\mathcal P}\mathbb Q[A(x)\xi\le b(x)]\ge1-\epsilon$ with $\mathcal P=\{\mathbb Q: d_W(\mathbb Q,\mathbb P)\le\delta\}$ → `ENNReal.ofReal (1 - ϵ) ≤ ⨅ ℚ ∈ ambiguityBall δ 1 P univ, ℚ (safeSet …)` in $[0,\infty]$, with $W_1$ valued in $[0,\infty]$; reason: the same condition: all values lie in $[0,1]$ and $1-\epsilon>0$; measures at infinite distance are outside the ball, so no moment condition restricts it
--   - encoding: $1-\epsilon\in(0,1)$, the standing assumption of p.1 → hypotheses `0 < ϵ` and `ϵ < 1`; reason: same range
--   - encoding: Definition 2: $\mathbb P$ on the Lebesgue subsets of a convex $\Omega$, Borel $A,B\subseteq\Omega$, $\mathbb P(\theta A+(1-\theta)B)\ge m_\alpha(\mathbb P(A),\mathbb P(B);\theta)$ → `IsAlphaConcaveMeasure α P`: all measurable $A,B\subseteq E$, $P$ evaluated on $\theta A+(1-\theta)B$ as Mathlib's outer measure, values compared through `toReal`; reason: equivalent: $\theta A+(1-\theta)B$ is analytic, so its outer measure is its Lebesgue (completion) measure; $\Omega$ is immaterial because $m_\alpha$ is nondecreasing in each argument; probabilities are finite
--   - encoding: $\alpha\in\overline{\mathbb R}$ → `α : EReal`; reason: same values $[-\infty,+\infty]$
--   - encoding: the set identity over all $x\in\mathbb R^n$ → an equivalence for each $x$ with $A(x)\ne0$; reason: $f(x,\cdot)$ is undefined when $A(x)=0$
--   - encoding: $\int_0^{\mathrm{VaR}_\epsilon(f(x,\zeta))}\cdots dt$ → the interval integral `∫ t in 0..v`, oriented; reason: the upper limit may be negative; the oriented integral is the meaning of the notation
--   - encoding: $\mathrm{VaR}_\epsilon$ of a random variable → `VaR ϵ` of its law (`P.map …`); reason: VaR depends only on the law
--   - encoding: $\min_{i\in[m]\setminus I(x)}$ → real infimum over the finite subtype of nonzero rows (`slack`); reason: nonempty under $A(x)\ne0$, so it is the minimum
-- source:
--   Shen, Jiang, Convex Chance-Constrained Programs with Wasserstein Ambiguity, arXiv:2111.02486v2, Proposition 2, (5)–(6), p.7

import Mathlib
import Definitions.Def_WassChanceCvx_IsAlphaConcaveMeasure
import Definitions.Def_WassChanceCvx_pessimisticSet
import Definitions.Def_WassChanceCvx_slack
import Definitions.Def_WassChanceCvx_VaR

open MeasureTheory

namespace WassChanceCvx

/-- **Proposition 2 (reformulation of `𝒳^p` for an α-concave reference).**
Shen, Jiang, arXiv:2111.02486v2, Proposition 2, p.7: "Suppose that `ℙ` is α-concave. Then, for
`δ > 0`, it holds that
`𝒳^p = {x ∈ ℝⁿ : δ ≤ ∫_0^{VaR_ϵ(f(x,ζ))} (ℙ[f(x, ζ) ≥ t] − (1 − ϵ)) dt` (5),
`ℙ[A(x)ζ ≤ b(x)] ≥ 1 − ϵ}` (6)."

**Formalization Note.** General affine `A(x)`, `b(x)`. Stated pointwise for `x` with
`A(x) ≠ 0`, where `f(x, ·)` is defined. `VaR_ϵ` is the lower `ϵ`-quantile of the law of
`f(x, ζ)`, `ζ ∼ P`. The integral in (5) is the oriented interval integral `∫ t in 0..v`: when
`v = VaR_ϵ(f(x, ζ)) < 0` it is `−∫_v^0`. `ϵ ∈ (0, 1)` is the standing assumption of p.1. -/
theorem proposition_2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {n k : ℕ}
    (A : (Fin n → ℝ) →ᵃ[ℝ] (Fin k → StrongDual ℝ E)) (b : (Fin n → ℝ) →ᵃ[ℝ] (Fin k → ℝ))
    (P : Measure E) [IsProbabilityMeasure P] (α : EReal) (hP : IsAlphaConcaveMeasure α P)
    (δ ϵ : ℝ) (hδ : 0 < δ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1) (x : Fin n → ℝ) (hA : A x ≠ 0) :
    x ∈ pessimisticSet A b P δ ϵ ↔
      (δ ≤ ∫ t in (0 : ℝ)..VaR ϵ (P.map (fun ζ => slack (A x) (b x) ζ)),
          ((P {ζ | t ≤ slack (A x) (b x) ζ}).toReal - (1 - ϵ))) ∧
        ENNReal.ofReal (1 - ϵ) ≤ P (safeSet (A x) (b x)) := by sorry

end WassChanceCvx
