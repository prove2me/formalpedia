-- Prove2me | Theorems.Thm_TRSHolderKL_lemma_2_1
-- name    : TRSHolderKL.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:52:44.075754+00:00
-- url     : https://prove2.me/theorems/c7f9f2fe-eb8f-4018-ae08-f303f1470f6a
-- title:
--   Lemma 2.1 — $S_0$ and $S_1$ for the nonconvex TRS
-- statement:
--   Let $A$ be a nonzero real symmetric $n\times n$ matrix ($n\ge2$), $b\in\mathbb R^n$, and suppose the smallest eigenvalue satisfies $\lambda_1<0$. Let $S_0$ be the optimal solution set of (P$_0$) and $S_1$ that of the convex relaxation (P$_1$) with objective $\tilde f(x)=x^T(A-\lambda_1I)x-2b^Tx+\lambda_1$. Then
--   1. $\|x^*\|=1$ for every $x^*\in S_0$;
--   2. $\tilde f(x^*)=f(x^*)$ for every $x^*\in S_0$;
--   3. $S_0=S_1\cap\{x\in\mathbb R^n:\|x\|=1\}$.
--
--   The lemma (from Flippo and Jansen) is what allows the nonconvex TRS to be analysed through the convex problem (P$_1$).
--
--   Differences from the source:
--   - encoding: ℝⁿ; an n × n nonzero real symmetric matrix A; λ₁ the smallest eigenvalue → EuclideanSpace ℝ (Fin n); A : Matrix with A.IsHermitian and A ≠ 0 acting by Matrix.toEuclideanLin; lam1 A the least element of the real spectrum; reason: Lean conventions; the same instances
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, Lemma 2.1, p.3

import Mathlib
import Definitions.Def_RBMSensitivity_E
import Definitions.Def_TRSHolderKL_f
import Definitions.Def_TRSHolderKL_S0
import Definitions.Def_TRSHolderKL_lam1
import Definitions.Def_TRSHolderKL_ftilde
import Definitions.Def_TRSHolderKL_S1

open scoped InnerProductSpace
open RBMSensitivity (E)

namespace TRSHolderKL

/-- Lemma 2.1, Jiang and Li, arXiv:1911.11955v2, p.3 (from Flippo and Jansen, Lemmas 1–2).
Suppose `λ₁ < 0`. Then every `x* ∈ S₀` has `‖x*‖ = 1`, `f̃(x*) = f(x*)` for every `x* ∈ S₀`,
and `S₀ = S₁ ∩ {x | ‖x‖ = 1}`.

**Formalization Note.** `ℝⁿ` is `EuclideanSpace ℝ (Fin n)`; `A` acts by
`Matrix.toEuclideanLin`; `λ₁` is the least element of the real spectrum of `A`. -/
theorem lemma_2_1 {n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hA0 : A ≠ 0) (b : E n) (hlam : lam1 A < 0) :
    (∀ x ∈ S0 A b, ‖x‖ = 1) ∧ (∀ x ∈ S0 A b, ftilde A b x = f A b x) ∧
      S0 A b = S1 A b ∩ {x | ‖x‖ = 1} := by sorry

end TRSHolderKL
