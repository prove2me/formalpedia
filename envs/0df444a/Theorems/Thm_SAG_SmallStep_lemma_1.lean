-- Prove2me | Theorems.Thm_SAG_SmallStep_lemma_1
-- name    : SAG.SmallStep.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:25:32.295748+00:00
-- url     : https://prove2.me/theorems/e7060c51-969b-4714-87da-a9be3911f0c8
-- title:
--   Lemma 1 — conditional expectation of a block quadratic form along one SAG step
-- statement:
--   Let $n\ge1$, let $f'_1,\dots,f'_n:\mathbb R^p\to\mathbb R^p$ and $x^*\in\mathbb R^p$ with $\sum_{i=1}^n f'_i(x^*)=0$, and let $\alpha\in\mathbb R$. Let $A\in\mathbb R^{np\times np}$ be symmetric, $b\in\mathbb R^{np\times p}$, and $c\in\mathbb R^{p\times p}$ symmetric, and $P=\begin{pmatrix}A&b\\ b^\top&c\end{pmatrix}$. Fix a SAG state $\theta^{k-1}=(y^{k-1},x^{k-1})$ and let $\theta^k$ be the state after one SAG step with step size $\alpha$ and index $i_k$ uniform on $\{1,\dots,n\}$. With $\theta^*=(f'(x^*),x^*)$ and $S=A-\frac{\alpha}{n}be^\top-\frac{\alpha}{n}eb^\top+\frac{\alpha^2}{n^2}ece^\top$,
--   $$
--   \begin{aligned}
--   \mathbb E\big[(\theta^k-\theta^*)^\top P(\theta^k-\theta^*)\,\big|\,\mathcal F_{k-1}\big]
--   &=(y^{k-1}-f'(x^*))^\top\Big[\Big(1-\frac2n\Big)S+\frac1n\mathrm{Diag}(\mathrm{diag}(S))\Big](y^{k-1}-f'(x^*))\\
--   &\quad+\frac1n(f'(x^{k-1})-f'(x^*))^\top\mathrm{Diag}(\mathrm{diag}(S))(f'(x^{k-1})-f'(x^*))\\
--   &\quad+\frac2n(y^{k-1}-f'(x^*))^\top[S-\mathrm{Diag}(\mathrm{diag}(S))](f'(x^{k-1})-f'(x^*))\\
--   &\quad+2\Big(1-\frac1n\Big)(y^{k-1}-f'(x^*))^\top\Big[b-\frac{\alpha}{n}ec\Big](x^{k-1}-x^*)\\
--   &\quad+\frac2n(f'(x^{k-1})-f'(x^*))^\top\Big[b-\frac{\alpha}{n}ec\Big](x^{k-1}-x^*)\\
--   &\quad+(x^{k-1}-x^*)^\top c\,(x^{k-1}-x^*).
--   \end{aligned}
--   $$
--   Here $f'(x)=(f'_1(x);\dots;f'_n(x))\in\mathbb R^{np}$ and the conditional expectation is the average over the $n$ possible indices.
--
--   Lemma 1 turns the expected one-step change of any quadratic Lyapunov function into an explicit quadratic form; both convergence proofs of the paper apply it with their own choice of $P$.
--
--   **Formalization Note** The conditional expectation given $\mathcal F_{k-1}$ is written as $\frac1n\sum_{i}$ of the quadratic form at `step f' α i θ`, for an arbitrary current state `θ`. Block matrices are as in `SAG.SmallStep.blockForm`. Three hypotheses the page uses without stating them are explicit: $A$ symmetric ($A_{ji}=A_{ij}^\top$), $c$ symmetric, and $\sum_i f'_i(x^*)=0$ (that is, $g'(x^*)=0$ for the minimizer $x^*$; the proof on p. 17 uses it to write $e^\top y^{k-1}$ as $e^\top(y^{k-1}-f'(x^*))$). No convexity or smoothness is needed. $n\ge1$ excludes the empty sum.
-- source:
--   Le Roux, Schmidt & Bach, A Stochastic Gradient Method with an Exponential Convergence Rate for Finite Training Sets, arXiv:1202.6258v4, p. 16, Lemma 1 (proof pp. 16–18)

import Mathlib
import Definitions.Def_SAG_SmallStep_run
import Definitions.Def_SAG_SmallStep_blockForm

open scoped RealInnerProductSpace

namespace SAG.SmallStep

/-- Lemma 1 (arXiv:1202.6258v4, p. 16). The conditional expectation, over the uniform index `i`,
of the block quadratic form `(θᵏ − θ*)ᵀ (A b; bᵀ c) (θᵏ − θ*)` after one SAG step from the current
state `θ = (y^{k−1}, x^{k−1})`. Here `u = y^{k−1} − f'(x*)`, `v = f'(x^{k−1}) − f'(x*)`,
`w = x^{k−1} − x*`. -/
theorem lemma_1 {p n : ℕ} (hn : 0 < n)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (xstar : EuclideanSpace ℝ (Fin p)) (hsum : ∑ i, f' i xstar = 0) (α : ℝ)
    (A : Fin n → Fin n → (EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)))
    (b : Fin n → (EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)))
    (c : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (hA : ∀ i j, ContinuousLinearMap.adjoint (A i j) = A j i)
    (hc : ContinuousLinearMap.adjoint c = c)
    (θ : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) :
    (1 / (n : ℝ)) * ∑ i, quadForm A b c (fun j => (step f' α i θ).1 j - f' j xstar)
        ((step f' α i θ).2 - xstar)
      = blockBil (fun i j => (1 - 2 / (n : ℝ)) • sMatrix α A b c i j
            + (1 / (n : ℝ)) • diagBlocks (sMatrix α A b c) i j)
          (fun i => θ.1 i - f' i xstar) (fun i => θ.1 i - f' i xstar)
        + (1 / (n : ℝ)) * blockBil (diagBlocks (sMatrix α A b c))
          (fun i => f' i θ.2 - f' i xstar) (fun i => f' i θ.2 - f' i xstar)
        + (2 / (n : ℝ)) * blockBil
          (fun i j => sMatrix α A b c i j - diagBlocks (sMatrix α A b c) i j)
          (fun i => θ.1 i - f' i xstar) (fun i => f' i θ.2 - f' i xstar)
        + 2 * (1 - 1 / (n : ℝ)) * colBil (bMinusEc α b c)
          (fun i => θ.1 i - f' i xstar) (θ.2 - xstar)
        + (2 / (n : ℝ)) * colBil (bMinusEc α b c)
          (fun i => f' i θ.2 - f' i xstar) (θ.2 - xstar)
        + ⟪θ.2 - xstar, c (θ.2 - xstar)⟫ := by sorry

end SAG.SmallStep
