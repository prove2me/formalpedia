-- Prove2me | Theorems.Thm_WassChanceCvx_theorem_1_pessimistic_rhs_convex_closed
-- name    : WassChanceCvx.theorem_1_pessimistic_rhs_convex_closed
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:28:12.276474+00:00
-- url     : https://prove2.me/theorems/dfd06832-2781-4e78-99b2-d0b7a2401831
-- title:
--   Theorem 1 — for an α-concave reference ($\alpha\ge-1$), $\mathcal X^p_{\mathrm R}$ is convex and closed
-- statement:
--   Let $E$ be a finite-dimensional real normed space with its Borel σ-algebra (the space $\mathbb R^q$ of the uncertain vector, with the norm of the Wasserstein distance). Let $A$ have rows $a_1,\dots,a_k$ (continuous linear functionals on $E$), let $b:\mathbb R^n\to\mathbb R^k$ be affine, let $\mathbb P$ be an α-concave Borel probability measure on $E$ with $\alpha\ge-1$, and let $\delta>0$ and $\epsilon\in(0,1)$. Let $\mathcal P$ be the type-1 Wasserstein ball of radius $\delta$ around $\mathbb P$, over all Borel probability measures on $E$. Then
--
--   $$
--   \mathcal X^p_{\mathrm R}=\Bigl\{x\in\mathbb R^n:\ \inf_{\mathbb Q\in\mathcal P}\mathbb Q\bigl[A\xi\le b(x)\bigr]\ge1-\epsilon\Bigr\}
--   $$
--
--   is convex and closed.
--
--   Around an empirical reference distribution the feasible region of this distributionally robust chance constraint is nonconvex in general. The theorem shows that it is convex as soon as the reference distribution is spread out in the sense of α-concavity (for instance log-concave, $\alpha=0$), so the robust constraint can be handled by convex optimization.
--
--   **Formalization Note** No density, support or moment hypothesis is placed on $\mathbb P$, and the rows are neither assumed nonzero nor normalized; the paper's normalizations on p.8 are made without loss of generality.
--
--   Differences from the source:
--   - encoding: ℝ^q (written ℝ^m in §3.1) with an arbitrary norm ‖·‖; rows $a_i$ with dual norm $\|a_i\|_*$ → a finite-dimensional real normed space $E$ with its Borel σ-algebra; rows are continuous linear functionals on $E$, $\|a_i\|_*$ their operator norm; reason: the same objects: ℝ^q with any norm is such a space and the dual norm is the operator norm
--   - generalization: $m$ rows with $\xi\in\mathbb R^m$ (§3.1) → $k$ rows, $k$ independent of $\dim E$ (including $k=0$); reason: (CC) on p.1 has $A(x)\in\mathbb R^{m\times q}$; $k=\dim E$ is the special case
--   - reading: $\mathcal P_0$ is the set of all probability distributions; $\Xi$ is the support of $\xi$ → all Borel probability measures on $E$; $\Xi=E$; reason: p.3 takes all probability distributions, and the proof of Theorem 1 (p.8) uses $d(\zeta,\mathcal S^c(x))=(f(x,\zeta))^+$ for every $\zeta\in\mathbb R^m$, which holds only when the unsafe set is taken in all of $\mathbb R^m$
--   - encoding: $\inf_{\mathbb Q\in\mathcal P}\mathbb Q[A(x)\xi\le b(x)]\ge1-\epsilon$ with $\mathcal P=\{\mathbb Q: d_W(\mathbb Q,\mathbb P)\le\delta\}$ → `ENNReal.ofReal (1 - ϵ) ≤ ⨅ ℚ ∈ ambiguityBall δ 1 P univ, ℚ (safeSet …)` in $[0,\infty]$, with $W_1$ valued in $[0,\infty]$; reason: the same condition: all values lie in $[0,1]$ and $1-\epsilon>0$; measures at infinite distance are outside the ball, so no moment condition restricts it
--   - encoding: $1-\epsilon\in(0,1)$, the standing assumption of p.1 → hypotheses `0 < ϵ` and `ϵ < 1`; reason: same range
--   - encoding: Definition 2: $\mathbb P$ on the Lebesgue subsets of a convex $\Omega$, Borel $A,B\subseteq\Omega$, $\mathbb P(\theta A+(1-\theta)B)\ge m_\alpha(\mathbb P(A),\mathbb P(B);\theta)$ → `IsAlphaConcaveMeasure α P`: all measurable $A,B\subseteq E$, $P$ evaluated on $\theta A+(1-\theta)B$ as Mathlib's outer measure, values compared through `toReal`; reason: equivalent: $\theta A+(1-\theta)B$ is analytic, so its outer measure is its Lebesgue (completion) measure; $\Omega$ is immaterial because $m_\alpha$ is nondecreasing in each argument; probabilities are finite
--   - encoding: $\alpha\in\overline{\mathbb R}$ → `α : EReal`; reason: same values $[-\infty,+\infty]$
--   - encoding: decision $x\in\mathbb R^n$; $b(x)\in\mathbb R^k$ affine in $x$ (p.1) → `Fin n → ℝ`; `b` an affine map into $\mathbb R^k$; reason: same data
-- source:
--   Shen, Jiang, Convex Chance-Constrained Programs with Wasserstein Ambiguity, arXiv:2111.02486v2, Theorem 1, p.8

import Mathlib
import Definitions.Def_WassChanceCvx_IsAlphaConcaveMeasure
import Definitions.Def_WassChanceCvx_pessimisticRHSSet

open MeasureTheory

namespace WassChanceCvx

/-- **Theorem 1 (convexity of the pessimistic joint chance constraint with RHS uncertainty).**
Shen, Jiang, *Convex Chance-Constrained Programs with Wasserstein Ambiguity*, arXiv:2111.02486v2,
Theorem 1, p.8: "Suppose that the reference distribution `ℙ` of `𝒫` is α-concave with `α ≥ −1`.
Then, for `δ > 0` the set `𝒳^p_R := {x ∈ ℝⁿ : inf_{ℚ∈𝒫} ℚ[Aξ ≤ b(x)] ≥ 1 − ϵ}` is convex and
closed."

**Formalization Note.** `ℝ^q` with the arbitrary norm of the Wasserstein distance (1) is a
finite-dimensional real normed space `E` with its Borel σ-algebra; the `k` rows of `A` are
continuous linear functionals on `E` (`k` is independent of `dim E`, and `k = 0` is allowed);
`b` is affine. `𝒫` is the type-1 Wasserstein ball of radius `δ` over all Borel probability
measures on `E` (`Ξ = ℝ^q`). `α` is an extended real; `ℙ` is any α-concave Borel probability
measure, with no density, support or moment hypothesis. `ϵ ∈ (0, 1)` is the standing assumption
of p.1. -/
theorem theorem_1_pessimistic_rhs_convex_closed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {n k : ℕ}
    (A : Fin k → StrongDual ℝ E) (b : (Fin n → ℝ) →ᵃ[ℝ] (Fin k → ℝ))
    (P : Measure E) [IsProbabilityMeasure P] (α : EReal) (hα : -1 ≤ α)
    (hP : IsAlphaConcaveMeasure α P) (δ ϵ : ℝ) (hδ : 0 < δ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1) :
    Convex ℝ (pessimisticRHSSet A b P δ ϵ) ∧ IsClosed (pessimisticRHSSet A b P δ ϵ) := by sorry

end WassChanceCvx
