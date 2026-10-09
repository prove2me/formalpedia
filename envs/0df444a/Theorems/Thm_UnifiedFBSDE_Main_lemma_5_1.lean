-- Prove2me | Theorems.Thm_UnifiedFBSDE_Main_lemma_5_1
-- name    : UnifiedFBSDE.Main.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:21:03.932971+00:00
-- url     : https://prove2.me/theorems/5da2e796-a260-4feb-9223-a6c47ed1b1f6
-- title:
--   Lemma 5.1, p. 20 — comparison: between two bounded super/sub-solutions the backward ODE (5.1) has a unique solution
-- statement:
--   Let $T>0$, let $F^0,F^1,F^2:[0,T]\times\mathbb R\to\mathbb R$ be measurable, $c^1,c^2:[0,T]\to\mathbb R$ integrable, and $h^0,h^1,h^2,C^1,C^2\in\mathbb R$. Consider
--
--   $$
--   y^0_t=h^0+\int_t^TF^0(s,y^0_s)\,ds,\tag{5.1}
--   $$
--   $$
--   y^1_t=h^1-C^1+\int_t^T[F^1(s,y^1_s)+c^1_s]\,ds,\qquad
--   y^2_t=h^2+C^2+\int_t^T[F^2(s,y^2_s)-c^2_s]\,ds.\tag{5.2}
--   $$
--
--   Assume:
--
--   1. $h^1\le h^0\le h^2$ and $F^1\le F^0\le F^2$;
--   2. the equations (5.2) have bounded solutions $y^1,y^2$ on $[0,T]$ with $y^1\le y^2$;
--   3. for each $t\in[0,T]$ the maps $y\mapsto F^i(t,y)$, $i=0,1,2$, are Lipschitz on $[y^1_t,y^2_t]$ with a common constant $L\ge0$;
--   4. $C^i\ge\int_t^Te^{-\int_s^T\alpha_r\,dr}c^i_s\,ds$ for all $t\in[0,T]$ and all measurable $\alpha$ with $|\alpha|\le L$.
--
--   Then (5.1) has a solution $y^0$ with $y^1\le y^0\le y^2$ on $[0,T]$, and it is the only solution of (5.1) lying between $y^1$ and $y^2$.
--
--   The lemma is the comparison tool behind Theorems 5.9–5.11: bounds on the dominating ODEs (3.13) are obtained by exhibiting explicit super- and sub-solutions.
--
--   **Formalization Note** Two hypotheses are added to the printed lemma. $y^1\le y^2$ on $[0,T]$ is implicit in the interval notation $[y^1_t,y^2_t]$; without it the lemma is false (with $F^i(t,y)=3|y|^{2/3}$, all constants $0$, $y^1_t=(T-t)^3$ and $y^2\equiv0$, condition (iii) holds vacuously but no $y^0$ lies between them). $L\ge0$ is implicit in "Lipschitz constant"; with $L<0$ hypothesis (iv) is vacuous and the lemma fails. The functions $\alpha$ in (iv) are taken measurable, and $c^i$ integrable on $[0,T]$ so that the integrals in (iv) are not Lean's junk value.
-- source:
--   Ma, Wu, Zhang and Zhang, On well-posedness of forward–backward SDEs—a unified approach, arXiv:1110.4658v2, pp. 19–20, (5.1), (5.2), Lemma 5.1

import Mathlib
import Definitions.Def_UnifiedFBSDE_Main_BackwardODE

open MeasureTheory Set

namespace UnifiedFBSDE.Main

theorem lemma_5_1 (T : ℝ) (hT : 0 < T) (F0 F1 F2 : ℝ → ℝ → ℝ)
    (hF0 : Measurable (Function.uncurry F0)) (hF1 : Measurable (Function.uncurry F1))
    (hF2 : Measurable (Function.uncurry F2))
    (c1 c2 : ℝ → ℝ) (hc1 : IntegrableOn c1 (Icc 0 T)) (hc2 : IntegrableOn c2 (Icc 0 T))
    (h0 h1 h2 C1 C2 L : ℝ) (hL : 0 ≤ L) (y1 y2 : ℝ → ℝ)
    -- (i)
    (hh : h1 ≤ h0 ∧ h0 ≤ h2)
    (hF : ∀ t ∈ Icc 0 T, ∀ y : ℝ, F1 t y ≤ F0 t y ∧ F0 t y ≤ F2 t y)
    -- (ii)
    (hy1 : SolvesBackwardODE T (h1 - C1) (fun s y => F1 s y + c1 s) y1) (hy1b : BoundedOn T y1)
    (hy2 : SolvesBackwardODE T (h2 + C2) (fun s y => F2 s y - c2 s) y2) (hy2b : BoundedOn T y2)
    (hy12 : ∀ t ∈ Icc 0 T, y1 t ≤ y2 t)
    -- (iii)
    (hLip : ∀ t ∈ Icc 0 T, ∀ y ∈ Icc (y1 t) (y2 t), ∀ y' ∈ Icc (y1 t) (y2 t),
      |F0 t y - F0 t y'| ≤ L * |y - y'| ∧ |F1 t y - F1 t y'| ≤ L * |y - y'| ∧
        |F2 t y - F2 t y'| ≤ L * |y - y'|)
    -- (iv)
    (hC1 : ∀ α : ℝ → ℝ, Measurable α → (∀ s, |α s| ≤ L) → ∀ t ∈ Icc 0 T,
      ∫ s in t..T, Real.exp (-∫ r in s..T, α r) * c1 s ≤ C1)
    (hC2 : ∀ α : ℝ → ℝ, Measurable α → (∀ s, |α s| ≤ L) → ∀ t ∈ Icc 0 T,
      ∫ s in t..T, Real.exp (-∫ r in s..T, α r) * c2 s ≤ C2) :
    ∃ y0 : ℝ → ℝ, SolvesBackwardODE T h0 F0 y0 ∧
      (∀ t ∈ Icc 0 T, y1 t ≤ y0 t ∧ y0 t ≤ y2 t) ∧
      ∀ y : ℝ → ℝ, SolvesBackwardODE T h0 F0 y → (∀ t ∈ Icc 0 T, y1 t ≤ y t ∧ y t ≤ y2 t) →
        ∀ t ∈ Icc 0 T, y t = y0 t := by sorry

end UnifiedFBSDE.Main
