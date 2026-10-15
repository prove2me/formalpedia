-- Prove2me | Theorems.Thm_QZeroSum19_GK_expected_potential_step
-- name    : QZeroSum19.GK.expected_potential_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T08:59:12.849975+00:00
-- url     : https://prove2.me/theorems/9146f981-8b2f-4be9-9589-a36c93dd2171
-- title:
--   Proof of Lemma 1, p. 4 — one iteration with η ∈ [0, 1/2] gives E[Φ(t+1)] ≤ Φ(t)(1 + 3η²)
-- statement:
--   Let $A\in[-1,1]^{n\times m}$, let $x\in\mathbb R^n$, $y\in\mathbb R^m$ be arbitrary iterates and let $0\le\eta\le 1/2$. Put $p=G(-A^{\mathsf T}x)\in\Delta^m$ and $q=G(Ay)\in\Delta^n$ (Gibbs distributions) and let $\Phi$ be the potential $\Phi(x,y)=\big(\sum_j e^{-(A^{\mathsf T}x)_j}\big)\big(\sum_i e^{(Ay)_i}\big)$. If $a\sim p$ and $b\sim q$ are drawn independently and the iterates are updated to $x+\eta e_b$, $y+\eta e_a$, then
--   $$\sum_{a\in[m]}\sum_{b\in[n]}p_a\,q_b\;\Phi(x+\eta e_b,\ y+\eta e_a)\ \le\ \Phi(x,y)\,\big(1+3\eta^2\big).$$
--
--   This is the one-step expectation bound $\mathbb E[\Phi(t+1)]\le\Phi(t)(1+3(\eta^{(t)})^2)$ of the proof of Lemma 1; iterating it controls the potential over a whole run.
--
--   **Formalization Note** The page uses $e^x\le1+x+3x^2/4$ on $x=\eta(A_{ia}-A_{bj})$, which requires $|\eta(A_{ia}-A_{bj})|\le1$; the hypothesis $0\le\eta\le1/2$ is the stated form of that requirement. Both step schedules of Algorithm 1 satisfy it.
-- source:
--   van Apeldoorn and Gilyén, Quantum algorithms for zero-sum games, arXiv:1904.03180v1, p. 4, proof of Lemma 1, last display

import Mathlib
import Definitions.Def_QZeroSum19_GK_Setting

open Matrix

namespace QZeroSum19.GK

/-- Proof of Lemma 1, p. 4, last display: one iteration with step `η ∈ [0, 1/2]`, sampling
`a ∼ p = G(−Aᵀx)` and `b ∼ q = G(Ay)` independently, satisfies `E[Φ(t + 1)] ≤ Φ(t)(1 + 3η²)`. -/
theorem expected_potential_step {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (hA : ∀ i j, |A i j| ≤ 1) (x : Fin n → ℝ) (y : Fin m → ℝ) (η : ℝ) (hη0 : 0 ≤ η)
    (hη1 : η ≤ 1 / 2) :
    ∑ a, ∑ b, gibbs (-(Aᵀ *ᵥ x)) a * gibbs (A *ᵥ y) b *
        potential A (x + η • Pi.single b 1) (y + η • Pi.single a 1) ≤
      potential A x y * (1 + 3 * η ^ 2) := by sorry

end QZeroSum19.GK
