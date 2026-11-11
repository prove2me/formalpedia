-- Prove2me | Theorems.Thm_QuantumTriangleFinding_Search_common_block_coordinates
-- name    : QuantumTriangleFinding.Search.common_block_coordinates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:27:12.552636+00:00
-- url     : https://prove2.me/theorems/1e57522b-958b-438e-b829-43015bde30ed
-- title:
--   Lemma 4.5 — A common block of coordinates
-- statement:
--   Use the forbidden-pattern law $\mu$ with $0<p\le1/2$. For a block $B\subseteq I$, put $L_B=\sum_{i\in B}D_i$ and $N_{i,B}(x)=\sum_{j\in B\setminus\{i\}}A_{ij}(x)$. Let $G_B$ depend only on coordinates outside $B$, with $\mu(G_B^c)\le b$, $0\le b\le1$. Assume $d\ge0$, $pd\le1/10$, and $N_{i,B}(x)\le d$ for every $i\in B$ and $x\in\operatorname{supp}\mu\cap G_B$.
--
--   For every family of positive semidefinite input-register operators $H_i\succeq L_B$ ($i\in B$), every $R>0$, and every joint vector $f$ in every finite workspace, put $F_B=(I+L_B/R)^{-1}$ and $F_i=(I+H_i/R)^{-1}$. Then
--   $$\sum_{i\in B}\|F_iD_if\|^2\le\sum_{i\in B}\langle D_if,F_BD_if\rangle\le3R\|f\|^2+|B|b\|f\|_\infty^2.$$
--   The infinity norm uses $\mu$. The good-event condition holds uniformly over all permitted assignments within each good outside fiber, and the empty block is included. Both parts of the inequality chain are retained.
--
--   Differences from the source:
--   - encoding: finite complex Hilbert spaces and square-root probability-weighted joint vectors → Euclidean workspaces and support functions with weighted inner products, norms and kernel adjoints; reason: choosing an orthonormal basis and sending f(x) to √ρ(x)f(x) is an isometric change of coordinates; every finite workspace is represented
-- source:
--   Arjan Cornelissen, Amin Shiraz Gilani, Xingyu Zhou, STOC 2027 submission #1375 (October 2026), Lemma 4.5, (4.25)–(4.26), pp. 22–23

import Definitions.Def_QuantumTriangleFinding_Search_ConditionalOperators

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace QuantumTriangleFinding.Search

/-- Lemma 4.5, pp.22–23. The good event is constant on entire outside-B fibers. -/
theorem common_block_coordinates {I W : Type} [Fintype I] [DecidableEq I] [Fintype W]
    (p : ℝ) (hp : 0 < p) (hp2 : p ≤ 1 / 2)
    (ℱ : Finset (Finset I)) (hℱ : ∀ C ∈ ℱ, C.Nonempty)
    (B : Finset I) (G : Set (I → Bool)) (hout : OutsideEvent B G)
    (b d : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hd : 0 ≤ d) (hpd : p * d ≤ 1 / 10)
    (hbad : eventProb (conditionedBernoulli p ℱ) Gᶜ ≤ b)
    (hcount : ∀ i ∈ B, ∀ x : Support (conditionedBernoulli p ℱ), x.val ∈ G →
      interactionCount ℱ B i x.val ≤ d)
    (H : I → Matrix (Support (conditionedBernoulli p ℱ)) (Support (conditionedBernoulli p ℱ)) ℂ)
    (hH : ∀ i ∈ B, Positive (conditionedBernoulli p ℱ) (H i) ∧
      OperatorLE (conditionedBernoulli p ℱ) (blockDifferences (conditionedBernoulli p ℱ) B) (H i))
    (R : ℝ) (hR : 0 < R) (f : Joint (conditionedBernoulli p ℱ) W) :
    let μ := conditionedBernoulli p ℱ
    let D := conditionalDifference μ
    let FB := resolvent (blockDifferences μ B) R
    (∑ i ∈ B, normSq μ (applyKernel (resolvent (H i) R) (applyKernel (D i) f))) ≤
      (∑ i ∈ B, (jointInner μ (applyKernel (D i) f) (applyKernel FB (applyKernel (D i) f))).re) ∧
    (∑ i ∈ B, (jointInner μ (applyKernel (D i) f) (applyKernel FB (applyKernel (D i) f))).re) ≤
      3 * R * normSq μ f + (B.card : ℝ) * b * infinityNorm μ f ^ 2 := by sorry

end QuantumTriangleFinding.Search
