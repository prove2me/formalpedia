-- Prove2me | Theorems.Thm_QueueingFundamentals_Numerical_uniformized_matrix_stochastic
-- name    : QueueingFundamentals.Numerical.uniformized_matrix_stochastic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T20:24:31.526229+00:00
-- url     : https://prove2.me/theorems/f313ef70-dad6-43c2-a95a-33686aa7e750
-- title:
--   Eq. (8.12) — the uniformized matrix $\tilde P = Q/\Lambda + I$ is stochastic
-- statement:
--   Let $Q$ be the generator of a continuous-time Markov chain on $\{0,1,\dots,N\}$, with off-diagonal rates $q_{ij}\ge 0$ and diagonal entries $-q_i$, $q_i=\sum_{j\ne i}q_{ij}$. Let $\Lambda>0$ satisfy $\Lambda\ge q_i$ for every state $i$, and let $\tilde P=Q/\Lambda+I$. Then the entries of $\tilde P$ are
--
--   $$\tilde p_{in}^{(1)}=\begin{cases} q_{in}/\Lambda & (i\ne n),\\ 1-q_i/\Lambda & (i=n),\end{cases}$$
--
--   and $\tilde P$ is a stochastic matrix: all entries are nonnegative and every row sums to one.
--
--   This makes $\tilde P$ the transition matrix of the discrete-parameter Markov chain $Y_k$ obtained by thinning a Poisson process of rate $\Lambda$, which is the basis of the randomization technique.
--
--   **Formalization Note** The book takes $\Lambda$ equal to $\max_i q_i$ ("the minimum diagonal element of $Q$", p.382); any $\Lambda\ge\max_i q_i$ works and is allowed here. The book prints $q_{ij}/\Lambda$ in (8.12) for the entry $(i,n)$; the index is corrected to $q_{in}$.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.384, Eq. (8.12) (with P̃ = Q/Λ + I, p.383, and Λ, p.382)

import Mathlib
import Definitions.Def_QueueingFundamentals_Numerical_Uniformization

open Matrix

namespace QueueingFundamentals.Numerical

/-- Eq. (8.12) (Gross et al., p.384): for a generator `Q` on `{0, …, N}` and any `Λ > 0` with
`Λ ≥ q_i` for every state `i`, the uniformized matrix `P̃ = Q/Λ + I` has entries
`p̃_in = q_in/Λ` (`i ≠ n`) and `p̃_ii = 1 − q_i/Λ`, and it is a stochastic matrix (the
transition matrix of the Markov chain `Y_k`). -/
theorem uniformized_matrix_stochastic {N : ℕ} (Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hQ : IsGenerator Q) (Λ : ℝ) (hΛ : 0 < Λ) (hΛq : ∀ i, exitRate Q i ≤ Λ) :
    (∀ i n, uniformizedMatrix Λ Q i n =
        if i ≠ n then Q i n / Λ else 1 - exitRate Q i / Λ) ∧
      IsStochastic (uniformizedMatrix Λ Q) := by sorry

end QueueingFundamentals.Numerical
