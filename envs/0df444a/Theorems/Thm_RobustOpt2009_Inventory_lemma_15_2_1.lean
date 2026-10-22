-- Prove2me | Theorems.Thm_RobustOpt2009_Inventory_lemma_15_2_1
-- name    : RobustOpt2009.Inventory.lemma_15_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:44:02.087417+00:00
-- url     : https://prove2.me/theorems/b57c0181-3c23-4ecb-b828-cf088a21cfa8
-- title:
--   Lemma 15.2.1 — extreme-scenario reduction for a multistage convex problem
-- statement:
--   Let $T$ be a finite horizon, let $D_t\subset\mathbb R^{n_t}$ be nonempty polytopes for $0\le t\le T$, and let $f_t:\mathbb R^{m_t}\to\mathbb R\cup\{+\infty\}$ be lower semicontinuous convex functions with polyhedral effective domains for $1\le t\le T+1$. Fix real linear maps $A_t,B_{t+1},C_{t+1}$, vectors $b_t$, and a real number $R$ of compatible dimensions. A policy $S_t(d^{t-1})$ depends only on the observations $d_0,\ldots,d_{t-1}$.
--
--   For a family of scenario sets $F_t$, let $\operatorname{Opt}(F)$ be the infimum of all real numbers $E$ achievable by a policy satisfying, for every $d^T\in F_0\times\cdots\times F_T$,
--   $$E\ge\sum_{t=1}^{T+1}f_t(S_t(d^{t-1})),\qquad A_1S_1(d^0)\ge b_1,$$
--   $$A_{t+1}S_{t+1}(d^t)\ge B_{t+1}d^t+C_{t+1}S_t(d^{t-1})+b_{t+1}\quad(1\le t\le T),$$
--   $$\|S_t(d^{t-1})\|_\infty\le R\quad(1\le t\le T).$$
--   Here $B_{t+1}$ multiplies the entire prefix $d^t$. Then
--   $$\operatorname{Opt}(D_0,\ldots,D_T)=\operatorname{Opt}(\operatorname{Ext}D_0,\ldots,\operatorname{Ext}D_T).$$
--
--   Thus replacing each uncertainty polytope by its extreme points preserves the optimal value over unrestricted policies with the given information pattern.
--
--   **Formalization Note** The optimal values are in `EReal`: infeasibility or the absence of a finite cost bound gives $+\infty$, and unboundedness below gives $-\infty$. This states equality of values, without adding attainment. Nonempty polytopes are finite convex hulls, including singleton and lower-dimensional cases. The statement allows zero horizon and zero-dimensional vector spaces; the same displayed systems specify those boundary cases. Costs never equal $-\infty$, and convexity is imposed on their effective domains. No measurability, affine-policy restriction, singleton assumption on $D_0$, sign assumption on $R$, or bound on $S_{T+1}$ is added. The concrete optimal-value expression is expanded in the theorem for a self-contained blind audit; a separate Lean type check compares it with the model definition.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, https://doi.org/10.1515/9781400831050, Lemma 15.2.1, printed p. 430 (PDF p. 456).

import Mathlib

open scoped BigOperators

namespace RobustOpt2009.Inventory

/-- Lemma 15.2.1, printed p. 430 (PDF p. 456). The concrete model is expanded
in this statement so its blind audit does not require resolving custom imports. -/
theorem lemma_15_2_1 {n m k : ℕ → ℕ} (T : ℕ)
    (A : (t : ℕ) → (Fin (m t) → ℝ) →ₗ[ℝ] (Fin (k t) → ℝ))
    (B : (t : ℕ) → ((j : Fin (t + 1)) → Fin (n j.val) → ℝ) →ₗ[ℝ]
      (Fin (k (t + 1)) → ℝ))
    (C : (t : ℕ) → (Fin (m t) → ℝ) →ₗ[ℝ] (Fin (k (t + 1)) → ℝ))
    (b : (t : ℕ) → Fin (k t) → ℝ)
    (f : (t : ℕ) → (Fin (m t) → ℝ) → EReal) (R : ℝ)
    (D : (t : ℕ) → Set (Fin (n t) → ℝ))
    (hD : ∀ t, t ≤ T → ∃ V : Finset (Fin (n t) → ℝ),
      V.Nonempty ∧ D t = convexHull ℝ (V : Set (Fin (n t) → ℝ)))
    (hf : ∀ t, 1 ≤ t → t ≤ T + 1 →
      (∀ x, f t x ≠ ⊥) ∧ LowerSemicontinuous (f t) ∧
      ConvexOn ℝ {x | f t x ≠ ⊤} (fun x => (f t x).toReal) ∧
      ∃ (q : ℕ) (G : Matrix (Fin q) (Fin (m t)) ℝ) (g : Fin q → ℝ),
        {x | f t x ≠ ⊤} = {x | G.mulVec x ≤ g}) :
    let value := fun (F : (t : ℕ) → Set (Fin (n t) → ℝ)) =>
      sInf {v : EReal | ∃ E : ℝ, v = (E : EReal) ∧
        ∃ S : (t : ℕ) → ((j : Fin t) → Fin (n j.val) → ℝ) → (Fin (m t) → ℝ),
        ∀ d : (j : Fin (T + 1)) → Fin (n j.val) → ℝ,
        (∀ j, d j ∈ F j.val) →
          (∑ t : Fin (T + 1), f (t.val + 1)
            (S (t.val + 1) (fun j => d ⟨j.val,
              lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt t.isLt)⟩))) ≤ (E : EReal) ∧
          b 1 ≤ A 1 (S 1 (fun j => d ⟨j.val,
            lt_of_lt_of_le j.isLt (Nat.succ_le_succ (Nat.zero_le T))⟩)) ∧
          (∀ t : ℕ, ∀ _ht : 1 ≤ t, ∀ hT : t ≤ T,
            B t (fun j => d ⟨j.val, lt_of_lt_of_le j.isLt (Nat.succ_le_succ hT)⟩) +
              C t (S t (fun j => d ⟨j.val,
                lt_of_lt_of_le j.isLt (Nat.le_trans hT (Nat.le_succ T))⟩)) + b (t + 1) ≤
              A (t + 1) (S (t + 1) (fun j => d ⟨j.val,
                lt_of_lt_of_le j.isLt (Nat.succ_le_succ hT)⟩))) ∧
          (∀ t : ℕ, ∀ _ht : 1 ≤ t, ∀ hT : t ≤ T,
            ‖S t (fun j => d ⟨j.val,
              lt_of_lt_of_le j.isLt (Nat.le_trans hT (Nat.le_succ T))⟩)‖ ≤ R)}
    value D = value (fun t => (D t).extremePoints ℝ) := by sorry

end RobustOpt2009.Inventory
