-- Prove2me | Theorems.Thm_WassChanceCvx_lemma_3_var_concave
-- name    : WassChanceCvx.lemma_3_var_concave
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:26:05.782341+00:00
-- url     : https://prove2.me/theorems/82f46a55-3ef4-4d98-bae4-e12b3ef252eb
-- title:
--   Lemma 3 — $x\mapsto\mathrm{VaR}_{1-\epsilon}(f(x,\zeta))$ is concave
-- statement:
--   Let $\zeta$ have an α-concave Borel probability distribution $\mathbb P$ on the finite-dimensional real normed space $E$, with $\alpha\ge-1$; let $A$ have $k\ge1$ rows $a_1,\dots,a_k$ (continuous linear functionals on $E$), $b:\mathbb R^n\to\mathbb R^k$ affine and $\epsilon\in(0,1)$. With $f(x,\zeta)=\min_{i\in[k]}\{b_i(x)-a_i^\top\zeta\}$, the map
--
--   $$
--   x\ \longmapsto\ \mathrm{VaR}_{1-\epsilon}\bigl(f(x,\zeta)\bigr)
--   $$
--
--   is concave on $\mathbb R^n$.
--
--   Its role in Theorem 1's proof is twofold: concavity makes the quantile continuous, and it makes the domain $\{(x,t): t\le\mathrm{VaR}(f(x,\zeta))\}$ of the integrand of (5) convex.
--
--   Differences from the source:
--   - encoding: ℝ^q (written ℝ^m in §3.1) with an arbitrary norm ‖·‖; rows $a_i$ with dual norm $\|a_i\|_*$ → a finite-dimensional real normed space $E$ with its Borel σ-algebra; rows are continuous linear functionals on $E$, $\|a_i\|_*$ their operator norm; reason: the same objects: ℝ^q with any norm is such a space and the dual norm is the operator norm
--   - encoding: Definition 2: $\mathbb P$ on the Lebesgue subsets of a convex $\Omega$, Borel $A,B\subseteq\Omega$, $\mathbb P(\theta A+(1-\theta)B)\ge m_\alpha(\mathbb P(A),\mathbb P(B);\theta)$ → `IsAlphaConcaveMeasure α P`: all measurable $A,B\subseteq E$, $P$ evaluated on $\theta A+(1-\theta)B$ as Mathlib's outer measure, values compared through `toReal`; reason: equivalent: $\theta A+(1-\theta)B$ is analytic, so its outer measure is its Lebesgue (completion) measure; $\Omega$ is immaterial because $m_\alpha$ is nondecreasing in each argument; probabilities are finite
--   - encoding: $\alpha\in\overline{\mathbb R}$ → `α : EReal`; reason: same values $[-\infty,+\infty]$
--   - generalization: rows normalized without loss of generality: $a_i\ne0$, $\|a_i\|_*=1$ (p.8) → arbitrary rows $a_i$; reason: the normalized case is the special case $\|a_i\|_*=1$
--   - encoding: $\min_{i\in[m]}$ → real infimum over `Fin k` with `0 < k`; reason: the minimum over an empty index set is undefined
--   - encoding: decision $x\in\mathbb R^n$; $b(x)\in\mathbb R^k$ affine in $x$ (p.1) → `Fin n → ℝ`; `b` an affine map into $\mathbb R^k$; reason: same data
--   - generalization: $m$ rows with $\xi\in\mathbb R^m$ (§3.1) → $k$ rows, $k$ independent of $\dim E$; reason: (CC) on p.1 has $A(x)\in\mathbb R^{m\times q}$; $k=\dim E$ is the special case
--   - encoding: $\mathrm{VaR}_{1-\epsilon}$ of a random variable → `VaR (1 - ϵ)` of its law (`P.map …`); reason: VaR depends only on the law
-- source:
--   Shen, Jiang, Convex Chance-Constrained Programs with Wasserstein Ambiguity, arXiv:2111.02486v2, Lemma 3 and the display of f, p.8

import Mathlib
import Definitions.Def_WassChanceCvx_IsAlphaConcaveMeasure
import Definitions.Def_WassChanceCvx_VaR

open MeasureTheory

namespace WassChanceCvx

/-- **Lemma 3 (concavity of the quantile of the slack).**
Shen, Jiang, arXiv:2111.02486v2, Lemma 3, p.8: "For all `ϵ ∈ (0, 1)`, if `ζ` has an α-concave
distribution with `α ≥ −1`, then `VaR_{1−ϵ}(f(x, ζ))` is concave in `x` on `ℝⁿ`", where (p.8)
`f(x, ζ) = min_{i∈[m]} {bᵢ(x) − aᵢᵀζ}`.

**Formalization Note.** `ζ ∼ P` on `E`; the `k ≥ 1` rows `aᵢ` of the constant matrix `A` are
continuous linear functionals and `b` is affine. The paper normalizes the rows (`aᵢ ≠ 0`,
`‖aᵢ‖_* = 1`, p.8, without loss of generality); the statement is made for arbitrary rows, which
contains the normalized case. `k ≥ 1` makes the minimum defined. -/
theorem lemma_3_var_concave
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {n k : ℕ} (hk : 0 < k)
    (A : Fin k → StrongDual ℝ E) (b : (Fin n → ℝ) →ᵃ[ℝ] (Fin k → ℝ))
    (P : Measure E) [IsProbabilityMeasure P] (α : EReal) (hα : -1 ≤ α)
    (hP : IsAlphaConcaveMeasure α P) (ϵ : ℝ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1) :
    ConcaveOn ℝ Set.univ
      (fun x : Fin n → ℝ => VaR (1 - ϵ) (P.map (fun ζ => ⨅ i, (b x i - A i ζ)))) := by sorry

end WassChanceCvx
