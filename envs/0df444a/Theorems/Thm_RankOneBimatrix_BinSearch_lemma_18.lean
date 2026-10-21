-- Prove2me | Theorems.Thm_RankOneBimatrix_BinSearch_lemma_18
-- name    : RankOneBimatrix.BinSearch.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:21.729557+00:00
-- url     : https://prove2.me/theorems/a60a5d1e-2085-4c4d-973d-5d55ccb58fd6
-- title:
--   Lemma 18, p. 18 — segment LP test
-- statement:
--   Let $\lambda_k$ be a breakpoint, $\lambda'$ a parameter in either adjacent segment, and $(x',v',s')$ an optimum of $P_{\lambda'}$. On the lower side, an optimum of $P^{\max}$ stays between $\lambda'$ and $\lambda_k$ and detects an equilibrium on the hyperplane. The upper side has the analogous statement for $P^{\min}$.
--
--   $$\exists(\lambda,x,y)\in\mathcal N\cap H\text{ in the tested interval}\Longleftrightarrow x^{*\top}a=\lambda^*\text{ at the auxiliary optimum}.$$
--
--   This is the segment test used by BINSEARCH. **Formalization Note** Missing predecessor or successor values encode $-\infty$ or $+\infty$.
-- source:
--   Adsul, Garg, Mehta, Sohoni, von Stengel, Fast Algorithms for Rank-1 Bimatrix Games, arXiv:1812.04611v4, p. 18, Lemma 18(a,b) and (39)

import Definitions.Def_RankOneBimatrix_BinSearch_Setting

namespace RankOneBimatrix.BinSearch
open Matrix

/-- Lemma 18(a,b), p. 18. Missing neighbors encode `-∞` and `+∞`. -/
theorem lemma_18 {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℝ) (a : Fin m → ℝ) (b : Fin n → ℝ)
    (lamK lam' : ℝ) (prev next : Option ℝ) (p' : PPoint m n)
    (hbreak : IsBreakpoint A b lamK)
    (hprev : PrevBreak A b lamK prev) (hnext : NextBreak A b lamK next)
    (hp' : p' ∈ POpt A b lam') :
    (InLeftInterval prev lamK lam' → lam' ≤ p'.1 ⬝ᵥ a →
      ∀ z ∈ PmaxOpt A a b (Mset A b lam') (Nset A b lam') lam',
        lam' ≤ z.1 ∧ z.1 ≤ lamK ∧
        ((∃ (lam : ℝ) (x : Fin m → ℝ) (y : Fin n → ℝ),
          lam' ≤ lam ∧ lam ≤ lamK ∧
          IsNE A (-A + onesLam lam b) x y ∧ x ⬝ᵥ a = lam) ↔
          z.2.1 ⬝ᵥ a = z.1 ∧
            ∃ y : Fin n → ℝ, IsNE A (-A + onesLam z.1 b) z.2.1 y)) ∧
    (InRightInterval lamK next lam' → p'.1 ⬝ᵥ a ≤ lam' →
      ∀ z ∈ PminOpt A a b (Mset A b lam') (Nset A b lam') lam',
        lamK ≤ z.1 ∧ z.1 ≤ lam' ∧
        ((∃ (lam : ℝ) (x : Fin m → ℝ) (y : Fin n → ℝ),
          lamK ≤ lam ∧ lam ≤ lam' ∧
          IsNE A (-A + onesLam lam b) x y ∧ x ⬝ᵥ a = lam) ↔
          z.2.1 ⬝ᵥ a = z.1 ∧
            ∃ y : Fin n → ℝ, IsNE A (-A + onesLam z.1 b) z.2.1 y)) := by sorry

end RankOneBimatrix.BinSearch
