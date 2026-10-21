-- Prove2me | Theorems.Thm_ShapleySnowSG_Kernel_prop_3_4_1
-- name    : ShapleySnowSG.Kernel.prop_3_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:00:52.869014+00:00
-- url     : https://prove2.me/theorems/71eab0a0-aa72-4431-b0f3-6c1afa95cd6c
-- title:
--   Proposition 3.4.1, p. 17 — a nonzero polynomial of degree ≤ rank(Δ̇⁰) vanishes at v^k_λ
-- statement:
--   In the setting of Proposition 3.2.1 (discounted stochastic game, $\lambda\in(0,1]$, values $v_\lambda$, a Shapley–Snow kernel of each local game $\mathcal G^k(\lambda,v_\lambda)$ and the resulting $\dot\Delta^0$), fix a state $k$. Then there is a polynomial $\dot P^k$ with real coefficients such that
--   $$\dot P^k(v^k_\lambda)=0,\qquad \dot P^k\not\equiv0,\qquad \deg\dot P^k\le\mathrm{rank}(\dot\Delta^0).$$
--
--   It is the univariate characterisation behind Theorem 3.4.2 (iii)–(iv).
--
--   **Formalization Note** As constructed in the proof on p. 17, the polynomial is the determinant of a square submatrix of the reduced pencil $\dot\Delta^k-w\dot\Delta^0$. This carries the content of the proposition, since allowing an arbitrary real polynomial would make its existence immediate. The degree bound uses only $\le\mathrm{rank}$ (the paper's proof quotes its reference [4, Proposition 4.6] as an equality, which fails for singular pencils; only the inequality is posed).
-- source:
--   Attia & Oliu-Barton, Shapley–Snow kernels, multiparameter eigenvalue problems and stochastic games, arXiv:1810.08798v2, p. 17, Proposition 3.4.1

import Mathlib
import Definitions.Def_ShapleySnowSG_Kernel_StochasticGame

namespace ShapleySnowSG.Kernel

open Matrix

/-- Proposition 3.4.1, p. 17: for every state `k` there is a polynomial `Ṗ^k ≢ 0` with
`Ṗ^k(v^k_λ) = 0` and `deg Ṗ^k ≤ rank(Δ̇^0)`. The proof constructs `Ṗ^k` as the determinant
of a square submatrix of the reduced pencil `Δ̇^k − w Δ̇^0`. -/
theorem prop_3_4_1 {n : ℕ} (hn : 0 < n) {I J : Fin n → Type*} [∀ k, Fintype (I k)] [∀ k, Fintype (J k)]
    [∀ k, Nonempty (I k)] [∀ k, Nonempty (J k)]
    (g : ∀ k, I k → J k → ℝ) (q : ∀ k, I k → J k → Fin n → ℝ)
    (hq0 : ∀ k i j l, 0 ≤ q k i j l) (hq1 : ∀ k i j, ∑ l, q k i j l = 1)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (v : Fin n → ℝ) (hv : IsShapleyFixed g q lam v)
    (s : Fin n → ℕ) (r : ∀ k, Fin (s k) ↪ I k) (c : ∀ k, Fin (s k) ↪ J k)
    (hK : ∀ k, IsSSK (localGame g q lam v k) (s k) (r k) (c k)) (k : Fin n) :
    ∃ (m : ℕ) (f h : Fin m ↪ (∀ k, Fin (s k))),
      let P : Polynomial ℝ :=
        ((DeltaDot g q lam s r c k.succ).map Polynomial.C -
          (Polynomial.X : Polynomial ℝ) • (DeltaDot g q lam s r c 0).map Polynomial.C).submatrix f h |>.det
      P.eval (v k) = 0 ∧ P ≠ 0 ∧
        P.natDegree ≤ (DeltaDot g q lam s r c 0).rank := by sorry

end ShapleySnowSG.Kernel
