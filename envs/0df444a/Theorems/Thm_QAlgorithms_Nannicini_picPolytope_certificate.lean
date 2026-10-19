-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_picPolytope_certificate
-- name    : QAlgorithms.Nannicini.picPolytope_certificate
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:53:04.77761+00:00
-- url     : https://prove2.me/theorems/5d5ff795-6d81-4fca-b680-08aa0b40f15f
-- title:
--   Emptiness of the PIC polytope certifies primal feasibility after rescaling
-- statement:
--   Consider the primal SDP
--
--   $$
--   \max\ \operatorname{Tr}(CX) \quad \text{s.t.}\quad \operatorname{Tr}(A^{(j)}X) \le b_j\ (j = 1,\dots,m),\quad X \succeq 0, \tag{P-SDP}
--   $$
--
--   with Hermitian $n\times n$ matrices $C, A^{(1)}, \dots, A^{(m)}$ and $b \in \mathbb{R}^m$, under the standing assumptions (a) $A^{(1)} = I$ and $b_1 = R > 0$, and (b) $\|C\| \le 1$. Fix $\gamma \in \mathbb{R}$ and $\epsilon > 0$, and for $X \succeq 0$ let
--
--   $$
--   P_\epsilon(X) = \Bigl\{ y \in \mathbb{R}^m : b^\top y \le \gamma,\ \operatorname{Tr}\Bigl(\bigl(\textstyle\sum_j y_j A^{(j)} - C\bigr)X\Bigr) \ge -\epsilon,\ y \ge 0 \Bigr\}.
--   $$
--
--   Let $X \succeq 0$.
--
--   1. If $P_\epsilon(X) = \emptyset$, then there is $z \ge 0$ such that $zX$ is feasible for (P-SDP) and $\operatorname{Tr}(C\,zX) \ge \gamma$.
--   2. If $P_\epsilon(X) \neq \emptyset$, then $X$ is not feasible for (P-SDP), or $\operatorname{Tr}(CX) \le \gamma + \epsilon$.
--
--   This is what makes the primal-infeasibility-certificate oracle useful: a failure yields a primal solution of value at least $\gamma$, a success yields a dual vector certifying that $X$ is not a good primal solution.
--
--   **Formalization Note** "Up to rescaling" is the scalar $z \ge 0$ of the source's proof (the optimal dual solution $z^*$ of the LP (8.18)). Traces are taken as real parts. Indices are 0-based in Lean, so $A^{(1)}, b_1$ sit at index $0$.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 188, Lemma 8.12. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Definitions.Def_QAlgorithms_Nannicini_Ch08a_Model
set_option autoImplicit false

namespace QAlgorithms.Nannicini

open QAlgorithms.SDP

open scoped ComplexOrder



/-- Nannicini p.188, Lemma 8.12 (Lem. 4.2 in [Arora and Kale, 2016]). Standing assumptions of
§8.2.2 (p.187): `C, A^(j)` Hermitian, (a) `A^(1) = I` and `b_1 = R > 0`, (b) `‖C‖ ≤ 1`. Let
`ϵ > 0`, `γ ∈ ℝ` and `X ⪰ 0`.
1. If `P_ϵ(X)` (Eq. (8.16)) is empty then, up to rescaling, `X` is feasible for (P-SDP) with
   objective value at least `γ`: some `z ≥ 0` makes `zX` primal feasible with `Tr(C zX) ≥ γ`.
2. If `P_ϵ(X)` is nonempty then `X` is not feasible for (P-SDP), or `Tr(CX) ≤ γ + ϵ`. -/
theorem picPolytope_certificate {n m : ℕ} (hm : 0 < m) (A : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (b : Fin m → ℝ) (C : Matrix (Fin n) (Fin n) ℂ) (R : ℝ)
    (hAherm : ∀ j, (A j).IsHermitian) (hCherm : C.IsHermitian)
    (hA1 : A ⟨0, hm⟩ = 1) (hb1 : b ⟨0, hm⟩ = R) (hR : 0 < R) (hC : specNorm C ≤ 1)
    (γ ε : ℝ) (hε : 0 < ε) (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.PosSemidef) :
    (picPolytope A b C γ ε X = ∅ →
      ∃ z : ℝ, 0 ≤ z ∧ PrimalFeasible A b ((z : ℂ) • X) ∧
        γ ≤ (C * ((z : ℂ) • X)).trace.re) ∧
    ((picPolytope A b C γ ε X).Nonempty →
      ¬ PrimalFeasible A b X ∨ (C * X).trace.re ≤ γ + ε) := by
  sorry






end QAlgorithms.Nannicini
