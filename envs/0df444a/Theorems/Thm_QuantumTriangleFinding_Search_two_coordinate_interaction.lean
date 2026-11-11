-- Prove2me | Theorems.Thm_QuantumTriangleFinding_Search_two_coordinate_interaction
-- name    : QuantumTriangleFinding.Search.two_coordinate_interaction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:26:56.408894+00:00
-- url     : https://prove2.me/theorems/817453a4-280f-4a3a-ae54-257ff3f51ab5
-- title:
--   Lemma 4.3 — Two-coordinate interaction
-- statement:
--   Let $I$ be finite, $\mathcal F$ a possibly empty family of nonempty forbidden subsets, and $0<p\le1/2$. Use $\mu=\nu_p(\cdot\mid\Omega)$ from the forbidden-pattern definition. For distinct coordinates $i,j$, let $A_{ij}$ be the computed interaction indicator and its diagonal operator. Every joint vector $f$ in every finite complex workspace satisfies
--   $$\|[D_i,D_j]f\|\le p\|A_{ij}f\|,$$
--   $$\|[D_i,D_j]f\|^2\le p^2(1+p)(\|A_{ij}D_if\|^2+\|A_{ij}D_jf\|^2).$$
--   Moreover,
--   $$D_iD_j+D_jD_i\succeq-pA_{ij}(D_i+D_j),\qquad \|([D_i,D_j]f)^x\|\le2pA_{ij}(x)\|f\|_\infty\quad(x\in\operatorname{supp}\mu).$$
--   Both conditional-resampling orders $E_iE_j$ and $E_jE_i$ preserve every coordinate outside $\{i,j\}$. This includes forced coordinates and overlapping forbidden patterns; the conditioned bits are not assumed independent.
--
--   Differences from the source:
--   - encoding: finite complex Hilbert spaces and square-root probability-weighted joint vectors → Euclidean workspaces and support functions with weighted inner products, norms and kernel adjoints; reason: choosing an orthonormal basis and sending f(x) to √ρ(x)f(x) is an isometric change of coordinates; every finite workspace is represented
--   - encoding: pointwise estimates for x ∈ Ω → pointwise estimates on supp μ; reason: 0 < p ≤ 1/2 gives positive product mass at every bit string, hence supp μ = Ω
-- source:
--   Arjan Cornelissen, Amin Shiraz Gilani, Xingyu Zhou, STOC 2027 submission #1375 (October 2026), Lemma 4.3, (4.17)–(4.20), p. 20

import Definitions.Def_QuantumTriangleFinding_Search_ConditionalOperators

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace QuantumTriangleFinding.Search

/-- Lemma 4.3, p.20: all four inequalities and both outside-coordinate preservation clauses. -/
theorem two_coordinate_interaction {I W : Type} [Fintype I] [DecidableEq I] [Fintype W]
    (p : ℝ) (hp : 0 < p) (hp2 : p ≤ 1 / 2)
    (ℱ : Finset (Finset I)) (hℱ : ∀ C ∈ ℱ, C.Nonempty)
    (i j : I) (hij : i ≠ j) :
    let μ := conditionedBernoulli p ℱ
    let Di := conditionalDifference μ i
    let Dj := conditionalDifference μ j
    let A := interactionOperator μ ℱ i j
    (∀ f : Joint μ W,
      jointNorm μ (applyKernel (commutator Di Dj) f) ≤ p * jointNorm μ (applyKernel A f) ∧
      normSq μ (applyKernel (commutator Di Dj) f) ≤
        p ^ 2 * (1 + p) * (normSq μ (applyKernel A (applyKernel Di f)) +
          normSq μ (applyKernel A (applyKernel Dj f))) ∧
      (∀ x : Support μ, ‖applyKernel (commutator Di Dj) f x‖ ≤
        2 * p * interaction ℱ i j x.val * infinityNorm μ f)) ∧
    OperatorLE μ (-(p : ℂ) • (A * (Di + Dj))) (Di * Dj + Dj * Di) ∧
    PreservesOutside μ {i, j} (conditionalAverage μ i * conditionalAverage μ j) ∧
    PreservesOutside μ {i, j} (conditionalAverage μ j * conditionalAverage μ i) := by sorry

end QuantumTriangleFinding.Search
