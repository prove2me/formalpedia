-- Prove2me | Theorems.Thm_ShapleySnowSG_Kernel_lemma_2_2_3
-- name    : ShapleySnowSG.Kernel.lemma_2_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:00:37.099449+00:00
-- url     : https://prove2.me/theorems/af104983-fd31-4b14-9729-13e532e5f234
-- title:
--   Lemma 2.2.3, p. 8 — all entries of (−1)ⁿΔ⁰ are at least λⁿ
-- statement:
--   Consider a discounted stochastic game with $n\ge1$ states, finite nonempty action sets, transition probabilities $q$ and discount factor $\lambda\in(0,1]$, and let $\Delta^0$ be the first auxiliary matrix of its data array $D(\lambda)$. Then every entry of $(-1)^n\Delta^0$ satisfies
--   $$\big((-1)^n\Delta^0\big)_{(i_1,\dots,i_n),(j_1,\dots,j_n)}\ \ge\ \lambda^n .$$
--
--   In particular all the entries of $\Delta^0$ are nonzero and of the same sign, which is what makes the equation $\mathrm{val}(\Delta^k-w\Delta^0)=0$ uniquely solvable.
--
--   **Formalization Note** The paper cites this lemma from its reference [2] and attributes it to the diagonal dominance of (H2). The payoff $g$ is arbitrary (it does not enter $\Delta^0$).
-- source:
--   Attia & Oliu-Barton, Shapley–Snow kernels, multiparameter eigenvalue problems and stochastic games, arXiv:1810.08798v2, p. 8, Lemma 2.2.3

import Mathlib
import Definitions.Def_ShapleySnowSG_Kernel_StochasticGame

namespace ShapleySnowSG.Kernel

open Matrix

/-- Lemma 2.2.3, p. 8: all the entries of `(−1)^n Δ^0` are at least `λ^n`. -/
theorem lemma_2_2_3 {n : ℕ} (hn : 0 < n) {I J : Fin n → Type*} [∀ k, Fintype (I k)] [∀ k, Fintype (J k)]
    [∀ k, Nonempty (I k)] [∀ k, Nonempty (J k)]
    (g : ∀ k, I k → J k → ℝ) (q : ∀ k, I k → J k → Fin n → ℝ)
    (hq0 : ∀ k i j l, 0 ≤ q k i j l) (hq1 : ∀ k i j, ∑ l, q k i j l = 1)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    ∀ i j, lam ^ n ≤ (-1) ^ n * Delta g q lam 0 i j := by sorry

end ShapleySnowSG.Kernel
