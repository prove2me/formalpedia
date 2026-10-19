-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_iterRefine_iterations
-- name    : QAlgorithms.Nannicini.iterRefine_iterations
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:52:14.784913+00:00
-- url     : https://prove2.me/theorems/36394936-b644-4c85-9f44-21dfd95be0fb
-- title:
--   Iterative refinement reaches residual ϵ in O(log 1/ϵ) iterations
-- statement:
--   Fix a per-iteration precision $\delta \in (0,1)$. There is a constant $C > 0$, depending only on $\delta$, with the following property.
--
--   Let $A \in \mathbb{C}^{N\times N}$, let $b \in \mathbb{C}^N$ with $\|b\| = 1$, and let $\epsilon \in (0, \delta)$. Run the iterative refinement scheme (Algorithm 5): $x^{(0)} = 0$, $r^{(0)} = b$, and while $\|r^{(k-1)}\| > \epsilon$ obtain a vector $\hat x^{(k)}$ with
--
--   $$
--   \Bigl\| A\hat x^{(k)} - \frac{r^{(k-1)}}{\|r^{(k-1)}\|} \Bigr\| \le \delta,
--   $$
--
--   then set $x^{(k)} = x^{(k-1)} + \|r^{(k-1)}\|\,\hat x^{(k)}$ and $r^{(k)} = b - A x^{(k)}$. The vectors $\hat x^{(k)}$ are arbitrary apart from this guarantee, which is required only at the iterations the loop executes. Then the loop stops after some number $K$ of iterations, meaning $\|r^{(k)}\| > \epsilon$ for every $k < K$, and
--
--   $$
--   K \le C \log\frac{1}{\epsilon}, \qquad \|A x^{(K)} - b\| \le \epsilon .
--   $$
--
--   The returned vector $x^* = x^{(K)}$ is therefore an $\epsilon$-precise solution obtained with $O(\log 1/\epsilon)$ calls to a solver of constant precision. This is what lets a solver whose cost grows with $1/\delta$, such as a quantum linear system algorithm followed by tomography, reach high precision cheaply.
--
--   **Formalization Note** The iterates are the frozen `iterRefineX A b xhat k`, and $\|\cdot\|$ is the Euclidean norm. The constant $C$ is quantified after $\delta$ and before $N, A, b, \epsilon$ and the solver outputs. Since $\epsilon < 1$, $\log(1/\epsilon) > 0$. The guarantee for $\hat x^{(k+1)}$ is assumed whenever $\|r^{(j)}\| > \epsilon$ for all $j \le k$, i.e. exactly while the loop runs.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 158, Proposition 7.9. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_BlockEncoding
import Definitions.Def_QAlgorithms_Nannicini_Ch07a_Model
set_option autoImplicit false

namespace QAlgorithms.Nannicini

/-- Nannicini Proposition 7.9 (p.158), iterative refinement (Alg. 5, p.158).

For a constant per-iteration precision `δ ∈ (0, 1)` there is a constant `C > 0` such that, for
every system `A x = b` with `‖b‖ = 1` and every target precision `ε ∈ (0, δ)`, whatever vectors
`x̂^(k)` the solver returns (subject to the guarantee
`‖A x̂^(k) − r^(k−1)/‖r^(k−1)‖‖ ≤ δ` at every iteration the loop actually executes), the loop of
Alg. 5 stops after `K ≤ C log(1/ε)` iterations and the returned `x^(K)` has `‖A x^(K) − b‖ ≤ ε`.
Here `x^(k) = iterRefineX A b xhat k` (`x^(0) = 0`,
`x^(k) = x^(k−1) + ‖r^(k−1)‖ x̂^(k)`) and `r^(k) = b − A x^(k)`. -/
theorem iterRefine_iterations (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (b : EuclideanSpace ℂ (Fin N)), ‖b‖ = 1 →
        ∀ ε : ℝ, 0 < ε → ε < δ →
          ∀ xhat : ℕ → EuclideanSpace ℂ (Fin N),
            (∀ k : ℕ, (∀ j ≤ k, ε < ‖b - act A (iterRefineX A b xhat j)‖) →
              ‖act A (xhat (k + 1)) - normalizedVec (b - act A (iterRefineX A b xhat k))‖ ≤ δ) →
            ∃ K : ℕ, (K : ℝ) ≤ C * Real.log (1 / ε) ∧
              (∀ k < K, ε < ‖b - act A (iterRefineX A b xhat k)‖) ∧
              ‖act A (iterRefineX A b xhat K) - b‖ ≤ ε := by
  sorry















end QAlgorithms.Nannicini
