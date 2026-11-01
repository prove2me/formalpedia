-- Prove2me | Theorems.Thm_WassChanceCvx_corollary_1
-- name    : WassChanceCvx.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:27:18.677489+00:00
-- url     : https://prove2.me/theorems/d9c715a0-8a03-4c72-bfce-10f1f5a65f0a
-- title:
--   Corollary 1 — $\mathcal X^p$ through the slack $f$: constraints (3)–(4)
-- statement:
--   In the setting of Proposition 1, let $f(x,\zeta)=\min_{i\notin I(x)}(b_i(x)-a_i(x)^\top\zeta)/\|a_i(x)\|_*$ with $I(x)=\{i:a_i(x)=0\}$, and $\zeta\sim\mathbb P$. Let $x\in\mathbb R^n$ satisfy
--
--   1. $A(x)\ne0$,
--   2. $a_i(x)=0\Rightarrow b_i(x)\ge0$ for every row $i$,
--   3. $\mathbb E[(-f(x,\zeta))^+]<\infty$.
--
--   Then $x\in\mathcal X^p$ if and only if
--
--   $$
--   \frac\delta\epsilon+\mathrm{CVaR}_{1-\epsilon}\bigl(-f(x,\zeta)\bigr)\le\frac1\epsilon\mathbb E\bigl[(-f(x,\zeta))^+\bigr]\quad(3)\qquad\text{and}\qquad 0\ge\mathrm{VaR}_{1-\epsilon}\bigl(-f(x,\zeta)\bigr)\quad(4).
--   $$
--
--   The two constraints are stated through the slack $f$, which is concave in $x$; this is the first step from the distance reformulation towards the convexity analysis.
--
--   Differences from the source:
--   - encoding: ℝ^q (written ℝ^m in §3.1) with an arbitrary norm ‖·‖; rows $a_i$ with dual norm $\|a_i\|_*$ → a finite-dimensional real normed space $E$ with its Borel σ-algebra; rows are continuous linear functionals on $E$, $\|a_i\|_*$ their operator norm; reason: the same objects: ℝ^q with any norm is such a space and the dual norm is the operator norm
--   - encoding: decision $x\in\mathbb R^n$; $A(x)\in\mathbb R^{m\times q}$ and $b(x)\in\mathbb R^m$ affine in $x$ → `Fin n → ℝ`; `A` an affine map into $k$-tuples of functionals on $E$, `b` an affine map into $\mathbb R^k$; reason: same data; $k$ rows of $A(x)$, each a functional on $E$
--   - reading: $\mathcal P_0$ is the set of all probability distributions; $\Xi$ is the support of $\xi$ → all Borel probability measures on $E$; $\Xi=E$; reason: p.3 takes all probability distributions, and the proof of Theorem 1 (p.8) uses $d(\zeta,\mathcal S^c(x))=(f(x,\zeta))^+$ for every $\zeta\in\mathbb R^m$, which holds only when the unsafe set is taken in all of $\mathbb R^m$
--   - encoding: $\inf_{\mathbb Q\in\mathcal P}\mathbb Q[A(x)\xi\le b(x)]\ge1-\epsilon$ with $\mathcal P=\{\mathbb Q: d_W(\mathbb Q,\mathbb P)\le\delta\}$ → `ENNReal.ofReal (1 - ϵ) ≤ ⨅ ℚ ∈ ambiguityBall δ 1 P univ, ℚ (safeSet …)` in $[0,\infty]$, with $W_1$ valued in $[0,\infty]$; reason: the same condition: all values lie in $[0,1]$ and $1-\epsilon>0$; measures at infinite distance are outside the ball, so no moment condition restricts it
--   - encoding: $1-\epsilon\in(0,1)$, the standing assumption of p.1 → hypotheses `0 < ϵ` and `ϵ < 1`; reason: same range
--   - encoding: the set identity over all $x\in\mathbb R^n$ → an equivalence for each $x$ with $A(x)\ne0$; reason: $f(x,\cdot)$ is undefined when $A(x)=0$
--   - generalization: the implication $a_i(x)=0\Rightarrow b_i(x)\ge0$ assumed without loss of generality (pp.6–7) → the implication required only at the decision $x$ considered; reason: the paper's standing assumption gives it at every $x$, so the statement contains the paper's
--   - encoding: no integrability hypothesis → $\mathbb E[(-f(x,\zeta))^+]<\infty$; reason: otherwise (3) compares $\infty$ with $\infty$; in Lean a non-integrable expectation would be $0$
--   - encoding: VaR and CVaR of a random variable; $\min_\gamma$ in Definition 5 → `VaR` and `CVaR` of its law (`P.map …`); the real infimum `⨅ γ`; reason: both depend only on the law, and the objective is bounded below and attains its minimum when the positive part is integrable and $\epsilon\in(0,1)$
--   - encoding: $\min_{i\in[m]\setminus I(x)}$ → real infimum over the finite subtype of nonzero rows (`slack`); reason: nonempty under $A(x)\ne0$, so it is the minimum
-- source:
--   Shen, Jiang, Convex Chance-Constrained Programs with Wasserstein Ambiguity, arXiv:2111.02486v2, Corollary 1, (3)–(4), p.7; standing implication and f, pp.6–7

import Mathlib
import Definitions.Def_WassChanceCvx_pessimisticSet
import Definitions.Def_WassChanceCvx_slack
import Definitions.Def_WassChanceCvx_VaR
import Definitions.Def_WassChanceCvx_CVaR

open MeasureTheory

namespace WassChanceCvx

/-- **Corollary 1 (reformulation of `𝒳^p` through the slack `f`).**
Shen, Jiang, arXiv:2111.02486v2, Corollary 1, p.7: "For `δ > 0`, it holds that
`𝒳^p = {x ∈ ℝⁿ : δ/ϵ + CVaR_{1−ϵ}(−f(x, ζ)) ≤ (1/ϵ)𝔼[(−f(x, ζ))⁺]` (3),
`0 ≥ VaR_{1−ϵ}(−f(x, ζ))}` (4)", with `f` the normalized slack of p.7 and `ζ ∼ ℙ`.

**Formalization Note.** General affine `A(x)`, `b(x)`; any Borel probability measure `P`. Stated
pointwise for `x` with `A(x) ≠ 0` (where `f(x, ·)` is defined), with the paper's standing
implication `aᵢ(x) = 0 ⇒ bᵢ(x) ≥ 0` (pp.6–7, "assuming the above implication without loss of
generality") required at that `x`, and with `𝔼[(−f(x, ζ))⁺] < ∞` (otherwise (3) compares `∞` with
`∞`). -/
theorem corollary_1
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {n k : ℕ}
    (A : (Fin n → ℝ) →ᵃ[ℝ] (Fin k → StrongDual ℝ E)) (b : (Fin n → ℝ) →ᵃ[ℝ] (Fin k → ℝ))
    (P : Measure E) [IsProbabilityMeasure P] (δ ϵ : ℝ) (hδ : 0 < δ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1)
    (x : Fin n → ℝ) (hA : A x ≠ 0) (himp : ∀ i, A x i = 0 → 0 ≤ b x i)
    (hint : Integrable (fun ζ => max (-slack (A x) (b x) ζ) 0) P) :
    x ∈ pessimisticSet A b P δ ϵ ↔
      (δ / ϵ + CVaR (1 - ϵ) (P.map (fun ζ => -slack (A x) (b x) ζ)) ≤
          (1 / ϵ) * ∫ ζ, max (-slack (A x) (b x) ζ) 0 ∂P) ∧
        0 ≥ VaR (1 - ϵ) (P.map (fun ζ => -slack (A x) (b x) ζ)) := by sorry

end WassChanceCvx
