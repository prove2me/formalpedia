-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_mmwuSDP_correct
-- name    : QAlgorithms.Nannicini.mmwuSDP_correct
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:52:55.628116+00:00
-- url     : https://prove2.me/theorems/2fadfa69-587f-409b-9cb6-f630539efce7
-- title:
--   Algorithm 7 (MMWU for SDP) returns a primal or a dual certificate
-- statement:
--   Consider the primal–dual SDP pair (P-SDP) $\max \operatorname{Tr}(CX)$ s.t. $\operatorname{Tr}(A^{(j)}X) \le b_j$, $X \succeq 0$, and (D-SDP) $\min b^\top y$ s.t. $\sum_j y_j A^{(j)} - C \succeq 0$, $y \ge 0$, with Hermitian $n \times n$ data, $n \ge 2$, under assumptions (a) $A^{(1)} = I$, $b_1 = R > 0$ and (b) $\|C\| \le 1$. Let $\gamma \in \mathbb{R}$, $\epsilon > 0$, $w > 0$, and let $\mathcal{O}$ be any $\text{PIC-Oracle}_{\epsilon/3}$ of width at most $w$: on every $X \succeq 0$ it reports failure exactly when $P_{\epsilon/3}(X) = \emptyset$, and otherwise returns some $y \in P_{\epsilon/3}(X)$ with $\|\sum_j y_j A^{(j)} - C\| \le w$.
--
--   Run Algorithm 7 with $\rho^{(1)} = I/n$,
--
--   $$
--   T = \Bigl\lceil \frac{9 w^2 R^2 \ln n}{\epsilon^2} \Bigr\rceil, \qquad \eta = \sqrt{\frac{\ln n}{T}},
--   $$
--
--   querying $\mathcal{O}$ at $R\rho^{(t)}$, setting $M^{(t)} = \frac1w(\sum_j y^{(t)}_j A^{(j)} - C)$ and updating $\rho^{(t+1)}$ to the Gibbs state of $-\eta\sum_{\tau \le t} M^{(\tau)}$. Then:
--
--   1. if the algorithm returns a matrix $X = R\rho^{(t)}$ (oracle failure), then some rescaling $zX$, $z \ge 0$, is feasible for (P-SDP) with $\operatorname{Tr}(C\,zX) \ge \gamma$;
--   2. if it returns the vector $\bar y = \frac1T\sum_{t=1}^T y^{(t)} + \frac{\epsilon}{R} e_1$, then $\bar y$ is feasible for (D-SDP) and $b^\top \bar y \le \gamma + \epsilon$.
--
--   One run of this algorithm answers, approximately, the feasibility question used in each step of binary search on the optimal value $\gamma$.
--
--   **Formalization Note** The rescaling of the primal output is the existential $z \ge 0$ of Lemma 8.12, since Algorithm 7 says only "after rescaling as described in Lem. 8.12". The hypothesis $n \ge 2$ is added: for $n = 1$ one has $\ln n = 0$, so $T = 0$ and $\eta = \sqrt{0/0}$; the loop never runs and $\frac{\epsilon}{R}e_1$ need not be dual feasible.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 189, Theorem 8.15. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Definitions.Def_QAlgorithms_Nannicini_Ch08a_Model
set_option autoImplicit false

namespace QAlgorithms.Nannicini

open QAlgorithms.SDP

open scoped ComplexOrder




/-- Nannicini pp.189–191, Theorem 8.15 (Thm. 4.4 in [Arora and Kale, 2016], Thm. 5 in
[van Apeldoorn, 2020]). Under assumptions (a) `A^(1) = I`, `b_1 = R > 0` and (b) `‖C‖ ≤ 1`, with
`ϵ > 0`, width bound `w > 0` and any `PIC-Oracle_{ϵ/3}` of width at most `w` (Defs. 8.11, 8.13),
Alg. 7 (`mmwuSDP`, with `T = ⌈9w²R² ln n/ϵ²⌉`, `η = √(ln n/T)`) returns either a matrix `X`
which, rescaled as in Lemma 8.12, is feasible for (P-SDP) with objective value at least `γ`, or a
vector `ȳ` feasible for (D-SDP) with `bᵀȳ ≤ γ + ϵ`.

Added hypothesis `n ≥ 2`: at `n = 1`, `ln n = 0`, so `T = 0` and `η = √(0/0)`; the loop never
runs and the returned `(ϵ/R) e_1` need not be dual feasible (`C = [1]`, `R = 1`, `ϵ = 1/2`,
`γ = 2`). The source's proof divides by `T` and by `ln n`. -/
theorem mmwuSDP_correct {n m : ℕ} (hn : 2 ≤ n) (hm : 0 < m)
    (A : Fin m → Matrix (Fin n) (Fin n) ℂ) (b : Fin m → ℝ) (C : Matrix (Fin n) (Fin n) ℂ)
    (R : ℝ) (hAherm : ∀ j, (A j).IsHermitian) (hCherm : C.IsHermitian)
    (hA1 : A ⟨0, hm⟩ = 1) (hb1 : b ⟨0, hm⟩ = R) (hR : 0 < R) (hC : specNorm C ≤ 1)
    (γ ε w : ℝ) (hε : 0 < ε) (hw : 0 < w)
    (O : Matrix (Fin n) (Fin n) ℂ → Option (Fin m → ℝ))
    (hO : IsPICOracle A b C γ (ε / 3) w O) :
    (∀ X : Matrix (Fin n) (Fin n) ℂ, mmwuSDP A C R ε w O = Sum.inl X →
      ∃ z : ℝ, 0 ≤ z ∧ PrimalFeasible A b ((z : ℂ) • X) ∧
        γ ≤ (C * ((z : ℂ) • X)).trace.re) ∧
    (∀ y : Fin m → ℝ, mmwuSDP A C R ε w O = Sum.inr y →
      DualFeasible A C y ∧ ∑ j, b j * y j ≤ γ + ε) := by
  sorry





end QAlgorithms.Nannicini
