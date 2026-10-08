-- Prove2me | Theorems.Thm_TaoAnDCA_TRS_theorem_3_7_iv
-- name    : TaoAnDCA.TRS.theorem_3_7_iv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:24:11.179419+00:00
-- url     : https://prove2.me/theorems/b4382827-cbac-4769-b87b-f1547626f4a3
-- title:
--   Theorem 3.7(iv), p. 488 — with bounded iterates, every limit point pairs with a cluster point into a critical pair of (P) and (D)
-- statement:
--   Let $g,h$, the simplified DCA sequences $\{x^k\}$, $\{y^k\}$ and the constants $\rho_1,\rho_2,\rho_1^*,\rho_2^*$ be as in Theorem 3.7(i). Suppose that $\alpha$ is finite and that $\{x^k\}$ and $\{y^k\}$ are bounded. Then for every limit point $x^*$ of $\{x^k\}$ there are a cluster point $y^*$ of $\{y^k\}$ and a subsequence $k_j$ along which $x^{k_j}\to x^*$ and $y^{k_j}\to y^*$, such that
--   1. $(x^*,y^*)\in[\partial g^*(y^*)\cap\partial h^*(y^*)]\times[\partial g(x^*)\cap\partial h(x^*)]$ and
--   $$(g-h)(x^*) = (h^*-g^*)(y^*) = \beta = \lim_{k\to+\infty}(g-h)(x^k);$$
--   2. $$\lim_{j\to+\infty}\{g(x^{k_j})+g^*(y^{k_j})\} = \lim_{j\to+\infty}\langle x^{k_j},y^{k_j}\rangle = \langle x^*,y^*\rangle.$$
--
--   Symmetrically, for every limit point $y^*$ of $\{y^k\}$ there are a cluster point $x^*$ of $\{x^k\}$ and a common subsequence with the same two properties.
--
--   In particular every limit point of the DCA iterates is a critical point of $g-h$ ($\partial g(x^*)\cap\partial h(x^*)\neq\emptyset$) with value $\beta$.
--
--   **Formalization Note.** A limit point is a cluster point (`MapClusterPt`). The page's "$\lim\{g(x^k)+g^*(y^k)\} = \lim\langle x^k,y^k\rangle$" is along the subsequence on which $x^k\to x^*$ and $y^k\to y^*$ (the proof says "for the sake of simplicity we write $\lim x^k = x^*$"), so both are stated along a common strictly increasing reindexing $\varphi$. $\beta$, the common limit of Theorem 3.7(iii), is written as the limit of $(g-h)(x^k)$. "$\alpha$ finite" is $\alpha\neq-\infty$.
-- source:
--   Pham Dinh & Le Thi, A d.c. optimization algorithm for solving the trust-region subproblem, SIAM J. Optim. 8 (1998), p. 488, §3.4, Theorem 3.7(iv)

import Mathlib
import Definitions.Def_TaoAnDCA_TRS_Setting

open Filter Topology

namespace TaoAnDCA.TRS

theorem theorem_3_7_iv {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal) (hgh : TaoAnDCA.GlobalOpt.DCStanding g h)
    (x y : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsSimplifiedDCARun g h x y)
    (ρ₁ ρ₂ ρ₁' ρ₂' : ℝ) (h₁ : IsRhoConvex g ρ₁) (h₂ : IsRhoConvex h ρ₂)
    (h₁' : IsRhoConvex (CondatPD.FinDim.conj g) ρ₁') (h₂' : IsRhoConvex (CondatPD.FinDim.conj h) ρ₂')
    (hα : TaoAnDCA.GlobalOpt.primalValue g h ≠ ⊥)
    (hxb : Bornology.IsBounded (Set.range x)) (hyb : Bornology.IsBounded (Set.range y)) :
    (∀ xs : EuclideanSpace ℝ (Fin n), MapClusterPt xs atTop x →
      ∃ ys : EuclideanSpace ℝ (Fin n), ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (x ∘ φ) atTop (𝓝 xs) ∧ Tendsto (y ∘ φ) atTop (𝓝 ys) ∧
        xs ∈ TaoAnDCA.GlobalOpt.subdiff (CondatPD.FinDim.conj g) ys ∩ TaoAnDCA.GlobalOpt.subdiff (CondatPD.FinDim.conj h) ys ∧
        ys ∈ TaoAnDCA.GlobalOpt.subdiff g xs ∩ TaoAnDCA.GlobalOpt.subdiff h xs ∧
        Tendsto (fun k => TaoAnDCA.GlobalOpt.dcSub g h (x k)) atTop (𝓝 (TaoAnDCA.GlobalOpt.dcSub g h xs)) ∧
        TaoAnDCA.GlobalOpt.dcSub g h xs = TaoAnDCA.GlobalOpt.dcSub (CondatPD.FinDim.conj h) (CondatPD.FinDim.conj g) ys ∧
        Tendsto (fun k => g (x (φ k)) + CondatPD.FinDim.conj g (y (φ k))) atTop
          (𝓝 ((inner ℝ xs ys : ℝ) : EReal))) ∧
    (∀ ys : EuclideanSpace ℝ (Fin n), MapClusterPt ys atTop y →
      ∃ xs : EuclideanSpace ℝ (Fin n), ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (x ∘ φ) atTop (𝓝 xs) ∧ Tendsto (y ∘ φ) atTop (𝓝 ys) ∧
        xs ∈ TaoAnDCA.GlobalOpt.subdiff (CondatPD.FinDim.conj g) ys ∩ TaoAnDCA.GlobalOpt.subdiff (CondatPD.FinDim.conj h) ys ∧
        ys ∈ TaoAnDCA.GlobalOpt.subdiff g xs ∩ TaoAnDCA.GlobalOpt.subdiff h xs ∧
        Tendsto (fun k => TaoAnDCA.GlobalOpt.dcSub g h (x k)) atTop (𝓝 (TaoAnDCA.GlobalOpt.dcSub g h xs)) ∧
        TaoAnDCA.GlobalOpt.dcSub g h xs = TaoAnDCA.GlobalOpt.dcSub (CondatPD.FinDim.conj h) (CondatPD.FinDim.conj g) ys ∧
        Tendsto (fun k => g (x (φ k)) + CondatPD.FinDim.conj g (y (φ k))) atTop
          (𝓝 ((inner ℝ xs ys : ℝ) : EReal))) := by sorry

end TaoAnDCA.TRS
