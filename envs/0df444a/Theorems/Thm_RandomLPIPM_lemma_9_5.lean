-- Prove2me | Theorems.Thm_RandomLPIPM_lemma_9_5
-- name    : RandomLPIPM.lemma_9_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:09:29.212987+00:00
-- url     : https://prove2.me/theorems/acce8f9c-fbff-4b3c-a123-89aed47b14e7
-- title:
--   Lemma 9.5 — projected gradient descent reaches $\|P\nabla\Phi(u_k)\|\le\varepsilon$ in $O(\log(n/\varepsilon))$ steps
-- statement:
--   Let $A$ have full row rank, $x>0$, $\mu>0$, $P=P_x$ and $\Phi=\Phi_{x,\mu}$. Let $\varepsilon\in(0,1/4]$ and let $u_0=0$, $u_{k+1}=u_k-\tfrac12P\nabla\Phi(u_k)$. If the global minimizer $u^*$ of $\Phi$ on $\ker(AX)$ satisfies $\|u^*\|_\infty\le1/4$, then there is an absolute constant $K$ such that some $k\le K\log(n/\varepsilon)$ satisfies
--   $$\|P\nabla\Phi(u_k)\|_2\le\varepsilon\qquad\text{and}\qquad\|u_k-u^*\|_2\le 2\,\|P\nabla\Phi(u_k)\|_2 .$$
--
--   Each re-centering of Algorithm 1 therefore costs $O(\log(n/\varepsilon))$ linear system solves.
--
--   Differences from the source:
--   - generalization: x strictly feasible for (LP) (with b, c from the strictly feasible pair (LP)) → any x > 0 and any cost c, no right-hand side b; reason: the proof uses only x > 0 and full row rank of A; the source's case is an instance
--   - encoding: it takes k = O(log(n/ε)) steps to find u_k with … → ∃ k ≤ K·log(n/ε) with both properties, K > 0 absolute (chosen before all data); reason: the meaning of O(·) here
--   - encoding: u_k ∈ ker(AX); the global minimizer of Φ on ker(AX) → A(x·u) = 0; any u* with A(x·u*) = 0 minimizing Φ over that subspace; reason: the same subspace; the minimizer is unique by Proposition 9.4
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), Lemma 9.5, p.79

import Mathlib
import Definitions.Def_RandomLPIPM_phi
import Definitions.Def_RandomLPIPM_pgdIter
import Definitions.Def_ColumnRandLP_Norms

open Matrix

namespace RandomLPIPM

/-- **Lemma 9.5 (projected gradient descent on `Φ`).** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), Lemma 9.5, p.79.

Let `ε ∈ (0, 1/4]`, `u_k ∈ ker(AX)`, `Δu_k = −P∇Φ(u_k)` and `u_{k+1} = u_k + Δu_k/2`. If the global
minimizer `u*` of `Φ` on `ker(AX)` satisfies `‖u*‖_∞ ≤ 1/4`, then starting from `u₀ := 0` it takes
`k = O(log(n/ε))` projected gradient descent steps to find `u_k` with `‖P∇Φ(u_k)‖ ≤ ε` and
`‖u_k − u*‖ ≤ 2‖P∇Φ(u_k)‖`.

**Formalization Note.** `P = P_x = I − XAᵀ(AX²Aᵀ)⁻¹AX` and `Φ = Φ_{x,μ}` (§9.2, p.78), `A` of full
row rank (p.76), `x > 0`, `μ > 0`; norms are Euclidean. The `O` constant `K` is absolute (chosen
before all data). -/
theorem lemma_9_5 :
    ∃ K : ℝ, 0 < K ∧ ∀ {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (c x : Fin n → ℝ) (μ : ℝ),
    A.rank = d → (∀ i, 0 < x i) → 0 < μ →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 →
    ∀ uStar : Fin n → ℝ, A *ᵥ (x * uStar) = 0 →
    (∀ v : Fin n → ℝ, A *ᵥ (x * v) = 0 → phi c x μ uStar ≤ phi c x μ v) →
    ColumnRandLP.supNorm uStar ≤ 1 / 4 →
    ∃ k : ℕ, (k : ℝ) ≤ K * Real.log (n / ε) ∧
      ColumnRandLP.l2Norm (Px A x *ᵥ gradPhi c x μ (pgdIter A c x μ k)) ≤ ε ∧
      ColumnRandLP.l2Norm (pgdIter A c x μ k - uStar) ≤
        2 * ColumnRandLP.l2Norm (Px A x *ᵥ gradPhi c x μ (pgdIter A c x μ k)) := by sorry

end RandomLPIPM
