-- Prove2me | Theorems.Thm_WassTwoStage_LP1_constraint_decomposition
-- name    : WassTwoStage.LP1.constraint_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:55:27.801304+00:00
-- url     : https://prove2.me/theorems/972a00db-a7db-4054-b8c1-429528c8d60c
-- title:
--   Last display of p. 23 — the constraint of (33) as $\mathcal O(K)$ linear constraints
-- statement:
--   Let $T\in\mathbb R^{M\times K}$ (the matrix $T(x)$ at a fixed first-stage decision), $W\in\mathbb R^{M\times N_2}$, $q\in\mathbb R^{N_2}$, $w_+,w_->0$ and $\lambda\ge 0$, and assume the recourse is sufficiently expensive: some $p\ge 0$ satisfies $W^\top p = q$. With $\|\cdot\|_*$ the dual norm of the gauge (31) and $e_k$ the $k$-th unit vector of $\mathbb R^K$,
--
--   $$\|T^\top p\|_*\le\lambda\ \ \forall p\in\mathbb R^M_+ : W^\top p = q$$
--   $$\iff\ \sup_{\substack{p\ge0\\ W^\top p=q}} e_k^\top T^\top p/w_+ \le \lambda\ \text{ and }\ \sup_{\substack{p\ge0\\ W^\top p=q}} -e_k^\top T^\top p/w_- \le\lambda\quad\forall k\in[K]$$
--   $$\iff\ \forall k\in[K]\ \exists\phi_k,\psi_k\in\mathbb R^{N_2}:\ q^\top\phi_k\le\lambda,\ q^\top\psi_k\le\lambda,\ Te_k/w_+\le W\phi_k,\ -Te_k/w_-\le W\psi_k.$$
--
--   The suprema are over the dual recourse polyhedron and may be $+\infty$. This is the step that turns problem (33) into the linear program (32).
--
--   **Formalization Note** Both equivalences are stated as a conjunction of two biconditionals. The suprema are extended reals. The statement is made for an arbitrary matrix $T$, which covers every value $T(x)$.
-- source:
--   Hanasusanto, Kuhn, Conic Programming Reformulations of Two-Stage Distributionally Robust Linear Programs over Wasserstein Balls, arXiv:1609.07505v3, §4.1, proof of Theorem 6, last display of p. 23 and first sentence of p. 24

import Mathlib
import Definitions.Def_WassTwoStage_LP1_Gauge

open Matrix

namespace WassTwoStage.LP1

/-- The decomposition of the last constraint of (33), Hanasusanto–Kuhn, arXiv:1609.07505v3,
§4.1, last display of p. 23 (with the justification on p. 24). Here `T` stands for `T(x)` at a fixed
first-stage decision, `λ ≥ 0`, `w₊, w₋ > 0`, and the recourse is sufficiently expensive
(`p ≥ 0`, `Wᵀp = q` is feasible). Then
`‖Tᵀp‖_* ≤ λ` for all `p ∈ ℝ^M_+` with `Wᵀp = q`
⟺ for all `k`: `sup_{p ≥ 0, Wᵀp = q} e_kᵀTᵀp / w₊ ≤ λ` and `sup_{p ≥ 0, Wᵀp = q} −e_kᵀTᵀp / w₋ ≤ λ`
⟺ for all `k` there are `φ_k, ψ_k ∈ ℝ^{N₂}` with `qᵀφ_k ≤ λ`, `qᵀψ_k ≤ λ`, `Te_k / w₊ ≤ Wφ_k`
and `−Te_k / w₋ ≤ Wψ_k`. -/
theorem constraint_decomposition {K M N₂ : ℕ} (T : Matrix (Fin M) (Fin K) ℝ)
    (W : Matrix (Fin M) (Fin N₂) ℝ) (q : Fin N₂ → ℝ) (wp wm lam : ℝ)
    (hwp : 0 < wp) (hwm : 0 < wm) (hlam : 0 ≤ lam)
    (hrec : ∃ p : Fin M → ℝ, 0 ≤ p ∧ Wᵀ *ᵥ p = q) :
    ((∀ p : Fin M → ℝ, 0 ≤ p → Wᵀ *ᵥ p = q → dualGauge wp wm (Tᵀ *ᵥ p) ≤ (lam : EReal)) ↔
      ∀ k : Fin K,
        (⨆ (p : Fin M → ℝ) (_ : 0 ≤ p ∧ Wᵀ *ᵥ p = q), (((Tᵀ *ᵥ p) k / wp : ℝ) : EReal))
            ≤ (lam : EReal) ∧
        (⨆ (p : Fin M → ℝ) (_ : 0 ≤ p ∧ Wᵀ *ᵥ p = q), ((-(Tᵀ *ᵥ p) k / wm : ℝ) : EReal))
            ≤ (lam : EReal)) ∧
    ((∀ k : Fin K,
        (⨆ (p : Fin M → ℝ) (_ : 0 ≤ p ∧ Wᵀ *ᵥ p = q), (((Tᵀ *ᵥ p) k / wp : ℝ) : EReal))
            ≤ (lam : EReal) ∧
        (⨆ (p : Fin M → ℝ) (_ : 0 ≤ p ∧ Wᵀ *ᵥ p = q), ((-(Tᵀ *ᵥ p) k / wm : ℝ) : EReal))
            ≤ (lam : EReal)) ↔
      ∀ k : Fin K, ∃ phi psi : Fin N₂ → ℝ,
        q ⬝ᵥ phi ≤ lam ∧ q ⬝ᵥ psi ≤ lam ∧
        (1 / wp) • (T *ᵥ Pi.single k 1) ≤ W *ᵥ phi ∧
        -((1 / wm) • (T *ᵥ Pi.single k 1)) ≤ W *ᵥ psi) := by sorry

end WassTwoStage.LP1
