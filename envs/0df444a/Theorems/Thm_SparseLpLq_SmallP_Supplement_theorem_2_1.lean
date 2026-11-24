-- Prove2me | Theorems.Thm_SparseLpLq_SmallP_Supplement_theorem_2_1
-- name    : SparseLpLq.SmallP.Supplement.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T07:11:57.979801+00:00
-- url     : https://prove2.me/theorems/1f827b22-3ba7-44b5-8f08-ecf3d338566e
-- title:
--   Theorem 2.1 — every x* ∈ SOL(A,b,σ,p,q): boundary property, ‖x*‖₀ = |J| = rank(A_J), two-sided ‖x*‖_∞ bounds, x*_J = (A_JᵀA_J)⁻¹A_Jᵀb at σ = 0
-- statement:
--   Let $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$, $1\le q\le\infty$, and assume the blanket assumptions of the paper (p. 1): $\sigma\ge0$, $\mathrm{FEA}(A,b,\sigma,q)=\{x:\|Ax-b\|_q\le\sigma\}\ne\emptyset$ and $\|b\|_q>\sigma$. Let $0\le p\le1$ and let $x^*\in\mathrm{SOL}(A,b,\sigma,p,q)$ be an optimal solution of (1.1) (for $p=0$ the objective is $\|x\|_0$). Put $\mathcal J:=\mathrm{supp}(x^*)=\{i: x^*_i\ne0\}$, let $A_{\mathcal J}$ be the columns of $A$ indexed by $\mathcal J$, and $\lambda_{\max}$, $\lambda_{\min}$ the largest and smallest eigenvalues of $A_{\mathcal J}^\top A_{\mathcal J}$. Then:
--
--   1. For $0<p\le1$, $\|Ax^*-b\|_q=\sigma$; for $p=0$ there is $\alpha\in(0,1]$ with $\|A(\alpha x^*)-b\|_q=\sigma$ and $\alpha'x^*\in\mathrm{SOL}(A,b,\sigma,0,q)$ for every $\alpha'\in[\alpha,1]$.
--   2. For $0\le p<1$, $\|x^*\|_0=|\mathcal J|=\mathrm{rank}(A_{\mathcal J})$.
--   3. For $0\le p<1$,
--   $$\frac{(\|b\|_q-\sigma)\,m^{\min\{\frac12-\frac1q,0\}}}{\sqrt{|\mathcal J|\,\lambda_{\max}(A_{\mathcal J}^\top A_{\mathcal J})}}\ \le\ \|x^*\|_\infty\ \le\ \frac{\sigma\, m^{\max\{\frac12-\frac1q,0\}}+\|b\|_2}{\sqrt{\lambda_{\min}(A_{\mathcal J}^\top A_{\mathcal J})}},$$
--   and when $\sigma=0$, $x^*_{\mathcal J}=(A_{\mathcal J}^\top A_{\mathcal J})^{-1}A_{\mathcal J}^\top b$.
--
--   The theorem says that optimal solutions sit on the boundary of the feasible set, have linearly independent support columns, and have entries bounded above and below in terms of the data. The upper bound gives (2.8), $\|x^*\|_\infty\le r$, used for the explicit threshold of Theorem 2.3.
--
--   **Formalization Note** $q\in[1,\infty]$ is an extended nonnegative real and $1/q$ is `(q⁻¹).toReal` ($1/\infty=0$, p. 3). The support is a `Finset` and $A_{\mathcal J}$ is indexed by it. The largest and smallest eigenvalues are the supremum and infimum of the real spectrum of the symmetric matrix $A_{\mathcal J}^\top A_{\mathcal J}$; under the blanket assumptions $\mathcal J\ne\emptyset$, so the spectrum is finite and nonempty. The inverse is Mathlib's matrix inverse, which is the true inverse because $A_{\mathcal J}$ has full column rank by part 2. No condition on $A$ is added and $\mathcal J\ne\emptyset$ is not assumed.
--
--   Differences from the source:
--   - encoding: 1 ≤ q ≤ ∞ with 1/∞ = 0 → q : ℝ≥0∞ with 1 ≤ q; 1/q is (q⁻¹).toReal; reason: same instances
--   - encoding: λ_max(A_JᵀA_J), λ_min(A_JᵀA_J), the largest and smallest eigenvalues → sSup and sInf of spectrum ℝ (A_Jᵀ * A_J); reason: A_JᵀA_J is real symmetric, so its real spectrum is its (finite) set of eigenvalues, nonempty because J ≠ ∅ under the blanket assumptions
--   - encoding: (A_JᵀA_J)^{−1} → Mathlib matrix inverse (A_Jᵀ * A_J)⁻¹; reason: it equals the true inverse whenever the matrix is invertible, which part (ii) guarantees
--   - encoding: J = supp(x*), A_J the submatrix of columns in J, x*_J the subvector, ‖x*‖_∞ → J a Finset of Fin n, A_J : Matrix (Fin m) J ℝ, fun j : J => x j, qNorm ⊤ x; reason: indices 0, …, n−1; same objects
-- source:
--   Yang, Chen & Xiang, Sparse solutions of a class of constrained optimization problems, arXiv:1907.00880v5, p. 4, Theorem 2.1 (with the range 0 ≤ p ≤ 1, 1 ≤ q ≤ ∞ of the sentence before it); proof pp. 5–6

import Mathlib
import Definitions.Def_SparseLpLq_SmallP_Setting

open scoped ENNReal Matrix

namespace SparseLpLq.SmallP.Supplement
open SparseLpLq.SmallP
theorem theorem_2_1 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ : ℝ)
    (q : ℝ≥0∞) (hq : 1 ≤ q) (hσ : 0 ≤ σ) (hfeas : (FEA A b σ q).Nonempty) (hb : σ < qNorm q b)
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) (x : Fin n → ℝ) (hx : x ∈ SOL A b σ p q) :
    let J : Finset (Fin n) := Finset.univ.filter (fun i => x i ≠ 0)
    let AJ : Matrix (Fin m) J ℝ := fun i j => A i j
    let lamMax : ℝ := sSup (spectrum ℝ (AJᵀ * AJ))
    let lamMin : ℝ := sInf (spectrum ℝ (AJᵀ * AJ))
    -- (i)
    ((0 < p → qNorm q (A *ᵥ x - b) = σ) ∧
      (p = 0 → ∃ α ∈ Set.Ioc (0 : ℝ) 1, qNorm q (A *ᵥ (α • x) - b) = σ ∧
        ∀ α' ∈ Set.Icc α 1, α' • x ∈ SOL A b σ 0 q)) ∧
    -- (ii)
    (p < 1 → lpObj 0 x = (J.card : ℝ) ∧ J.card = AJ.rank) ∧
    -- (iii)
    (p < 1 →
      (qNorm q b - σ) * (m : ℝ) ^ (min (1 / 2 - (q⁻¹).toReal) 0) /
          Real.sqrt ((J.card : ℝ) * lamMax) ≤ qNorm ⊤ x ∧
        qNorm ⊤ x ≤ (σ * (m : ℝ) ^ (max (1 / 2 - (q⁻¹).toReal) 0) + qNorm 2 b) /
          Real.sqrt lamMin ∧
        (σ = 0 → (fun j : J => x j) = (AJᵀ * AJ)⁻¹ *ᵥ (AJᵀ *ᵥ b))) := by sorry
end SparseLpLq.SmallP.Supplement
