-- Prove2me | Theorems.Thm_SAG_LargeStep_lemma_1
-- name    : SAG.LargeStep.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:25:10.667984+00:00
-- url     : https://prove2.me/theorems/af37f64c-a6fe-47e5-b44a-1bfac77f168f
-- title:
--   Lemma 1 — conditional expectation of a block quadratic form along one SAG step
-- statement:
--   Throughout, $f_1,\dots,f_n:\mathbb R^p\to\mathbb R$ ($n\ge1$) are convex and differentiable with $L$-Lipschitz gradients $f_i'$, the average $g=\frac1n\sum_i f_i$ is $\mu$-strongly convex ($x\mapsto g(x)-\frac\mu2\|x\|^2$ is convex, $\mu>0$), $x^*$ minimizes $g$, $g'=\frac1n\sum_i f_i'$ and $\sigma^2=\frac1n\sum_i\|f_i'(x^*)\|^2$.
--
--   Let $\alpha\in\mathbb R$, and let $P=\begin{pmatrix}A&b\\ b^\top&c\end{pmatrix}$ with $A\in\mathbb R^{np\times np}$ and $c\in\mathbb R^{p\times p}$ symmetric and $b\in\mathbb R^{np\times p}$. Let $\theta^{k-1}=(y^{k-1},x^{k-1})$ be any state, $\theta^k$ the state after one SAG step with step size $\alpha$ and a uniformly random index, $\mathcal F_{k-1}$ the past, $f'(x)=(f_1'(x),\dots,f_n'(x))$ and $e=(I,\dots,I)^\top$. With
--   $$S=A-\frac\alpha n be^\top-\frac\alpha n eb^\top+\frac{\alpha^2}{n^2}ece^\top,$$
--   we have
--   $$\begin{aligned}\mathbb E\big[(\theta^k-\theta^*)^\top P(\theta^k-\theta^*)\,\big|\,\mathcal F_{k-1}\big]
--   &=(y^{k-1}-f'(x^*))^\top\Big[\big(1-\tfrac2n\big)S+\tfrac1n\mathrm{Diag}(\mathrm{diag}(S))\Big](y^{k-1}-f'(x^*))\\
--   &\quad+\tfrac1n(f'(x^{k-1})-f'(x^*))^\top\mathrm{Diag}(\mathrm{diag}(S))(f'(x^{k-1})-f'(x^*))\\
--   &\quad+\tfrac2n(y^{k-1}-f'(x^*))^\top\big[S-\mathrm{Diag}(\mathrm{diag}(S))\big](f'(x^{k-1})-f'(x^*))\\
--   &\quad+2\big(1-\tfrac1n\big)(y^{k-1}-f'(x^*))^\top\big[b-\tfrac\alpha n ec\big](x^{k-1}-x^*)\\
--   &\quad+\tfrac2n(f'(x^{k-1})-f'(x^*))^\top\big[b-\tfrac\alpha n ec\big](x^{k-1}-x^*)\\
--   &\quad+(x^{k-1}-x^*)^\top c\,(x^{k-1}-x^*).\end{aligned}$$
--   Here $\mathrm{Diag}(\mathrm{diag}(S))$ is the block-diagonal part of $S$.
--
--   Lemma 1 computes the expected quadratic part of both of the paper's Lyapunov functions after one step.
--
--   **Formalization Note** The conditional expectation is the average over the $n$ possible indices of the step from the fixed state $(y,x)$. Matrices are given by $p\times p$ blocks (continuous linear maps); symmetry of $A$ and $c$, which the proof uses and the lemma leaves implicit, is stated through inner products. The identity $\sum_if_i'(x^*)=0$, which the proof also uses, follows from the standing assumptions.
-- source:
--   Le Roux, Schmidt & Bach, A Stochastic Gradient Method with an Exponential Convergence Rate for Finite Training Sets, arXiv:1202.6258v4, p. 16, Lemma 1

import Mathlib
import Definitions.Def_SAG_LargeStep_setting
import Definitions.Def_SAG_LargeStep_sagRun
import Definitions.Def_SAG_LargeStep_blockQuad

namespace SAG.LargeStep

/-- Lemma 1, p. 16: the conditional expectation, over the uniform index of one SAG step from the
state `(y, x) = θᵏ⁻¹`, of the block quadratic form `(θᵏ − θ*)ᵀ (A b; bᵀ c) (θᵏ − θ*)`, for
symmetric `A` and `c`, with `S = A − (α/n) beᵀ − (α/n) ebᵀ + (α²/n²) eceᵀ`. -/
theorem lemma_1 {p n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L μ : ℝ)
    (xstar : EuclideanSpace ℝ (Fin p)) (h : Assumptions f f' L μ xstar)
    (α : ℝ)
    (A : Fin n → Fin n → EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (b : Fin n → EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (c : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (hA : ∀ (i j : Fin n) (u v : EuclideanSpace ℝ (Fin p)),
      inner ℝ u (A i j v) = inner ℝ (A j i u) v)
    (hc : ∀ u v : EuclideanSpace ℝ (Fin p), inner ℝ u (c v) = inner ℝ (c u) v)
    (y : Fin n → EuclideanSpace ℝ (Fin p)) (x : EuclideanSpace ℝ (Fin p)) :
    (1 / (n : ℝ)) * ∑ i, blockQuad A b c
        (fun j => (sagStep f' α (y, x) i).1 j - f' j xstar) ((sagStep f' α (y, x) i).2 - xstar)
      = (1 - 2 / (n : ℝ)) * ∑ i, ∑ j,
            inner ℝ (y i - f' i xstar) (blockS A b c α i j (y j - f' j xstar))
        + 1 / (n : ℝ) * ∑ i, inner ℝ (y i - f' i xstar) (blockS A b c α i i (y i - f' i xstar))
        + 1 / (n : ℝ) * ∑ i,
            inner ℝ (f' i x - f' i xstar) (blockS A b c α i i (f' i x - f' i xstar))
        + 2 / (n : ℝ) * (∑ i, ∑ j,
              inner ℝ (y i - f' i xstar) (blockS A b c α i j (f' j x - f' j xstar))
            - ∑ i, inner ℝ (y i - f' i xstar) (blockS A b c α i i (f' i x - f' i xstar)))
        + 2 * (1 - 1 / (n : ℝ)) * ∑ i,
            inner ℝ (y i - f' i xstar) ((b i - (α / (n : ℝ)) • c) (x - xstar))
        + 2 / (n : ℝ) * ∑ i,
            inner ℝ (f' i x - f' i xstar) ((b i - (α / (n : ℝ)) • c) (x - xstar))
        + inner ℝ (x - xstar) (c (x - xstar)) := by sorry

end SAG.LargeStep
