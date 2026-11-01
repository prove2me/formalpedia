-- Prove2me | Theorems.Thm_WassChanceCvx_proposition_3
-- name    : WassChanceCvx.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:26:22.865372+00:00
-- url     : https://prove2.me/theorems/ff54716b-1254-4d09-aa2c-c6829338b79d
-- title:
--   Proposition 3 — $H(x)=\mathbb P[A\xi\le b(x)]$ is α-concave and $\{H\ge1-\epsilon\}$ is convex and closed
-- statement:
--   Let $\xi$ have an α-concave Borel probability distribution $\mathbb P$ on the finite-dimensional real normed space $E$, $\alpha\in[-\infty,+\infty]$; let $A$ have rows $a_1,\dots,a_k$ (continuous linear functionals on $E$), let $b:\mathbb R^n\to\mathbb R^k$ be affine and $\epsilon\in(0,1)$. Put $H(x)=\mathbb P[A\xi\le b(x)]$ and $\mathcal D=\{x\in\mathbb R^n:\exists\xi,\ A\xi\le b(x)\}$. Then
--
--   1. $\mathcal D$ is convex;
--   2. $H$ is α-concave on $\mathcal D$;
--   3. $\mathcal X=\{x\in\mathbb R^n: \mathbb P[A\xi\le b(x)]\ge1-\epsilon\}$ is convex;
--   4. $\mathcal X$ is closed.
--
--   This is the classical convexity result of Prékopa and Shapiro–Dentcheva–Ruszczyński for chance constraints with right-hand-side uncertainty, and the base case that Theorem 1 extends to Wasserstein ambiguity.
--
--   Differences from the source:
--   - encoding: ℝ^q (written ℝ^m in §3.1) with an arbitrary norm ‖·‖; rows $a_i$ with dual norm $\|a_i\|_*$ → a finite-dimensional real normed space $E$ with its Borel σ-algebra; rows are continuous linear functionals on $E$, $\|a_i\|_*$ their operator norm; reason: the same objects: ℝ^q with any norm is such a space and the dual norm is the operator norm
--   - encoding: Definition 2: $\mathbb P$ on the Lebesgue subsets of a convex $\Omega$, Borel $A,B\subseteq\Omega$, $\mathbb P(\theta A+(1-\theta)B)\ge m_\alpha(\mathbb P(A),\mathbb P(B);\theta)$ → `IsAlphaConcaveMeasure α P`: all measurable $A,B\subseteq E$, $P$ evaluated on $\theta A+(1-\theta)B$ as Mathlib's outer measure, values compared through `toReal`; reason: equivalent: $\theta A+(1-\theta)B$ is analytic, so its outer measure is its Lebesgue (completion) measure; $\Omega$ is immaterial because $m_\alpha$ is nondecreasing in each argument; probabilities are finite
--   - encoding: $\alpha\in\overline{\mathbb R}$ → `α : EReal`; reason: same values $[-\infty,+\infty]$
--   - encoding: $1-\epsilon\in(0,1)$, the standing assumption of p.1 → hypotheses `0 < ϵ` and `ϵ < 1`; reason: same range
--   - reading: $H$ is α-concave on the set $\mathcal D$ → also concludes that $\mathcal D$ is convex; reason: Definition 1 defines α-concavity only on convex sets, so the printed clause presupposes the convexity of $\mathcal D$
--   - encoding: decision $x\in\mathbb R^n$; $b(x)\in\mathbb R^k$ affine in $x$ (p.1) → `Fin n → ℝ`; `b` an affine map into $\mathbb R^k$; reason: same data
--   - generalization: $m$ rows with $\xi\in\mathbb R^m$ (§3.1) → $k$ rows, $k$ independent of $\dim E$; reason: (CC) on p.1 has $A(x)\in\mathbb R^{m\times q}$; $k=\dim E$ is the special case
-- source:
--   Shen, Jiang, Convex Chance-Constrained Programs with Wasserstein Ambiguity, arXiv:2111.02486v2, Proposition 3, p.8

import Mathlib
import Definitions.Def_WassChanceCvx_IsAlphaConcaveOn
import Definitions.Def_WassChanceCvx_IsAlphaConcaveMeasure
import Definitions.Def_WassChanceCvx_safeSet

open MeasureTheory

namespace WassChanceCvx

/-- **Proposition 3 (classical chance constraint with RHS uncertainty, after SDR09).**
Shen, Jiang, arXiv:2111.02486v2, Proposition 3, p.8: "If `ξ ∈ ℝ^m` follows an α-concave
probability distribution, then `H(x) := ℙ[Aξ ≤ b(x)]` is α-concave on the set
`𝒟 := {x ∈ ℝⁿ : ∃ ξ such that Aξ ≤ b(x)}` and the following set is convex and closed:
`𝒳 := {x ∈ ℝⁿ : ℙ[Aξ ≤ b(x)] ≥ 1 − ϵ}`."

The conclusion has four clauses: `𝒟` is convex, `H` is α-concave on `𝒟`, and `𝒳` is convex and
closed.

**Formalization Note.** `ξ ∼ P` on `E` (`ℝ^m` with a norm); the `k` rows of `A` are continuous
linear functionals; `b` is affine; `α` is any extended real. The convexity of `𝒟` is stated
because Definition 1 defines α-concavity on convex sets only. `ϵ ∈ (0, 1)` is the standing
assumption of p.1. -/
theorem proposition_3
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {n k : ℕ}
    (A : Fin k → StrongDual ℝ E) (b : (Fin n → ℝ) →ᵃ[ℝ] (Fin k → ℝ))
    (P : Measure E) [IsProbabilityMeasure P] (α : EReal) (hP : IsAlphaConcaveMeasure α P)
    (ϵ : ℝ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1) :
    Convex ℝ {x : Fin n → ℝ | (safeSet A (b x)).Nonempty} ∧
      IsAlphaConcaveOn α {x : Fin n → ℝ | (safeSet A (b x)).Nonempty}
        (fun x => (P (safeSet A (b x))).toReal) ∧
      Convex ℝ {x : Fin n → ℝ | ENNReal.ofReal (1 - ϵ) ≤ P (safeSet A (b x))} ∧
      IsClosed {x : Fin n → ℝ | ENNReal.ofReal (1 - ϵ) ≤ P (safeSet A (b x))} := by sorry

end WassChanceCvx
