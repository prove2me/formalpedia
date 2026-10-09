-- Prove2me | Theorems.Thm_UnifiedFBSDE_Cubic_lemma_5_1
-- name    : UnifiedFBSDE.Cubic.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:16:03.381978+00:00
-- url     : https://prove2.me/theorems/e732739c-3de1-448e-a517-1170b34cbff8
-- title:
--   Lemma 5.1, p. 20 — comparison: between two bounded super/sub-solutions the backward ODE (5.1) has a unique solution
-- statement:
--   Let $T>0$ and let $F^0,F^1,F^2:\mathbb R\times\mathbb R\to\mathbb R$ be measurable. Let $c^1,c^2$ be integrable on $[0,T]$, and let $h^0,h^1,h^2,C^1,C^2\in\mathbb R$ and $L\ge 0$. Consider the backward ODEs on $[0,T]$
--   $$
--   y^0_t=h^0+\int_t^T F^0(s,y^0_s)\,ds, \tag{5.1}
--   $$
--   $$
--   y^1_t=h^1-C^1+\int_t^T[F^1(s,y^1_s)+c^1_s]\,ds,\qquad y^2_t=h^2+C^2+\int_t^T[F^2(s,y^2_s)-c^2_s]\,ds. \tag{5.2}
--   $$
--   Assume:
--   1. $h^1\le h^0\le h^2$, and $F^1(t,y)\le F^0(t,y)\le F^2(t,y)$ for $t\in[0,T]$, $y\in\mathbb R$;
--   2. the two equations (5.2) have bounded solutions $y^1$ and $y^2$ on $[0,T]$, with $y^1_t\le y^2_t$ for $t\in[0,T]$;
--   3. for each $t\in[0,T]$ and $i=0,1,2$, $y\mapsto F^i(t,y)$ is Lipschitz on $[y^1_t,y^2_t]$ with constant $L$;
--   4. for $i=1,2$: $C^i\ge\int_t^T e^{-\int_s^T\alpha_r\,dr}c^i_s\,ds$ for all $t\in[0,T]$ and all measurable $\alpha$ with $|\alpha|\le L$.
--
--   Then (5.1) has a solution $y^0$ with $y^1\le y^0\le y^2$ on $[0,T]$, and any solution of (5.1) that lies between $y^1$ and $y^2$ on $[0,T]$ coincides with $y^0$ there.
--
--   This comparison principle is the tool behind the sufficiency halves of Theorems 5.3 and 5.4: a solution is trapped between a sub- and a super-solution.
--
--   **Formalization Note.** Three hypotheses are made explicit that the page leaves implicit. (a) $y^1\le y^2$ on $[0,T]$: the page writes $[y^1_t,y^2_t]$ as an interval, and without it the lemma is false ($F^i=3|y|^{2/3}$, all constants zero, $y^1_t=(T-t)^3$, $y^2\equiv0$). (b) $L\ge0$, as befits a Lipschitz constant; with $L<0$ condition 4 is vacuous and the lemma fails. (c) $c^1,c^2$ are integrable on $[0,T]$, so that the integrals in condition 4 are genuine integrals. $F^i$ is taken measurable on all of $\mathbb R\times\mathbb R$; only its values for $t\in[0,T]$ matter. The same lemma is restated in the companion missions of this paper.
-- source:
--   Ma, Wu, Zhang and Zhang, On well-posedness of forward–backward SDEs—a unified approach, arXiv:1110.4658v2, pp. 19–20, (5.1), (5.2), Lemma 5.1

import Mathlib
import Definitions.Def_UnifiedFBSDE_Cubic_Setting

namespace UnifiedFBSDE.Cubic

/-- Lemma 5.1, p. 20 (comparison for the backward ODEs (5.1)–(5.2)). The hypothesis
`hy₁₂ : y¹ ≤ y²` on `[0, T]` is a disclosed addition: the lemma writes `[y¹_t, y²_t]` as an
interval and is false without it. -/
theorem lemma_5_1 (T : ℝ) (hT : 0 < T) (F₀ F₁ F₂ : ℝ → ℝ → ℝ)
    (hF₀ : Measurable (Function.uncurry F₀)) (hF₁ : Measurable (Function.uncurry F₁))
    (hF₂ : Measurable (Function.uncurry F₂))
    (c₁ c₂ : ℝ → ℝ) (hc₁ : MeasureTheory.IntegrableOn c₁ (Set.Icc 0 T))
    (hc₂ : MeasureTheory.IntegrableOn c₂ (Set.Icc 0 T))
    (h₀ h₁ h₂ C₁ C₂ L : ℝ) (hL : 0 ≤ L) (y₁ y₂ : ℝ → ℝ)
    -- (i)
    (hh : h₁ ≤ h₀ ∧ h₀ ≤ h₂)
    (hF : ∀ t ∈ Set.Icc 0 T, ∀ y : ℝ, F₁ t y ≤ F₀ t y ∧ F₀ t y ≤ F₂ t y)
    -- (ii)
    (hy₁ : IsBoundedSolution (fun s y => F₁ s y + c₁ s) (h₁ - C₁) T y₁)
    (hy₂ : IsBoundedSolution (fun s y => F₂ s y - c₂ s) (h₂ + C₂) T y₂)
    (hy₁₂ : ∀ t ∈ Set.Icc 0 T, y₁ t ≤ y₂ t)
    -- (iii)
    (hLip : ∀ t ∈ Set.Icc 0 T, ∀ y ∈ Set.Icc (y₁ t) (y₂ t), ∀ y' ∈ Set.Icc (y₁ t) (y₂ t),
      |F₀ t y - F₀ t y'| ≤ L * |y - y'| ∧ |F₁ t y - F₁ t y'| ≤ L * |y - y'| ∧
        |F₂ t y - F₂ t y'| ≤ L * |y - y'|)
    -- (iv)
    (hC₁ : CondIV L C₁ c₁ T) (hC₂ : CondIV L C₂ c₂ T) :
    ∃ y₀ : ℝ → ℝ, IsSolution F₀ h₀ T y₀ ∧
      (∀ t ∈ Set.Icc 0 T, y₁ t ≤ y₀ t ∧ y₀ t ≤ y₂ t) ∧
      ∀ y : ℝ → ℝ, IsSolution F₀ h₀ T y → (∀ t ∈ Set.Icc 0 T, y₁ t ≤ y t ∧ y t ≤ y₂ t) →
        ∀ t ∈ Set.Icc 0 T, y t = y₀ t := by sorry

end UnifiedFBSDE.Cubic
