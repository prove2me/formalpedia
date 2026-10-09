-- Prove2me | Theorems.Thm_UnifiedFBSDE_Rational_lemma_5_1
-- name    : UnifiedFBSDE.Rational.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:14:54.621978+00:00
-- url     : https://prove2.me/theorems/d878b1dc-7e42-4b52-bdb0-135ccfab2417
-- title:
--   Lemma 5.1, p. 20 — comparison: between two bounded super/sub-solutions the backward ODE (5.1) has a unique solution
-- statement:
--   Fix $T$ and measurable functions $F^0,F^1,F^2:[0,T]\times\mathbb R\to\mathbb R$, functions $c^1,c^2$ of time, and reals $h^0,h^1,h^2,C^1,C^2,L$. Consider the backward ODEs
--   $$
--   y^0_t=h^0+\int_t^TF^0(s,y^0_s)\,ds,\qquad(5.1)
--   $$
--   $$
--   y^1_t=h^1-C^1+\int_t^T[F^1(s,y^1_s)+c^1_s]\,ds,\qquad y^2_t=h^2+C^2+\int_t^T[F^2(s,y^2_s)-c^2_s]\,ds.\qquad(5.2)
--   $$
--   Assume:
--
--   1. $h^1\le h^0\le h^2$ and $F^1\le F^0\le F^2$ on $[0,T]\times\mathbb R$;
--   2. both equations in (5.2) have bounded solutions $y^1,y^2$ on $[0,T]$, with $y^1_t\le y^2_t$ for all $t\in[0,T]$;
--   3. for each $t\in[0,T]$ the maps $y\mapsto F^i(t,y)$, $i=0,1,2$, are Lipschitz on $[y^1_t,y^2_t]$ with a common constant $L\ge0$;
--   4. $c^1,c^2$ are integrable on $[0,T]$ and $C^i\ge\int_t^Te^{-\int_s^T\alpha_r\,dr}c^i_s\,ds$ for all $t\in[0,T]$ and every measurable $\alpha$ with $|\alpha|\le L$.
--
--   Then (5.1) has a solution $y^0$ on $[0,T]$ with $y^1\le y^0\le y^2$, and any solution of (5.1) lying between $y^1$ and $y^2$ coincides with it on $[0,T]$.
--
--   This comparison lemma is the tool behind every sufficiency argument for the dominating ODE.
--
--   **Formalization Note** Four readings are disclosed. (a) The hypothesis $y^1\le y^2$ is added: the page writes $[y^1_t,y^2_t]$ as an interval, and without it the lemma fails ($F^i=3|y|^{2/3}$, all constants $0$, $y^1_t=(T-t)^3$, $y^2\equiv0$). (b) $c^1,c^2$ are assumed integrable on $[0,T]$, so that the integrals in (iv) are meaningful. (c) "all $\alpha$ satisfying $|\alpha|\le L$" ranges over measurable $\alpha:\mathbb R\to\mathbb R$. (d) The Lipschitz constant satisfies $L\ge0$: with $L<0$ hypothesis (iv) is vacuous and (iii) holds on a one-point band, and the statement fails ($y^1=y^2\equiv-1$, $C^1=1$, $C^2=-1$, all other data $0$). Solutions carry explicit integrability of their integrands. The lemma is restated here; missions 1 and 2 of this series state it in their own namespaces.
-- source:
--   Ma, Wu, Zhang and Zhang, On well-posedness of forward–backward SDEs—a unified approach, arXiv:1110.4658v2, p. 20, Lemma 5.1, with (5.1) p. 19 and (5.2) p. 20

import Mathlib
import Definitions.Def_UnifiedFBSDE_Rational_Setting

namespace UnifiedFBSDE.Rational

/-- Lemma 5.1, p. 20 (comparison for the backward ODEs (5.1)–(5.2)), with the disclosed
additions `y1 ≤ y2` on `[0, T]`, `0 ≤ L` (a Lipschitz constant), and integrability of `c1, c2` (so that (iv) is meaningful). -/
theorem lemma_5_1 (T : ℝ) (F0 F1 F2 : ℝ → ℝ → ℝ) (c1 c2 : ℝ → ℝ)
    (h0 h1 h2 C1 C2 L : ℝ) (y1 y2 : ℝ → ℝ)
    (hF0 : Measurable (Function.uncurry F0)) (hF1 : Measurable (Function.uncurry F1))
    (hF2 : Measurable (Function.uncurry F2))
    -- (i)
    (hh : h1 ≤ h0 ∧ h0 ≤ h2)
    (hF : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y : ℝ, F1 s y ≤ F0 s y ∧ F0 s y ≤ F2 s y)
    -- (ii)
    (hy1 : UnifiedFBSDE.Cubic.IsSolution (fun s y => F1 s y + c1 s) (h1 - C1) T y1)
    (hy1b : ∃ M : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, |y1 t| ≤ M)
    (hy2 : UnifiedFBSDE.Cubic.IsSolution (fun s y => F2 s y - c2 s) (h2 + C2) T y2)
    (hy2b : ∃ M : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, |y2 t| ≤ M)
    (hy12 : ∀ t ∈ Set.Icc (0 : ℝ) T, y1 t ≤ y2 t)
    -- (iii)
    (hL : 0 ≤ L)
    (hLip : ∀ G ∈ ({F0, F1, F2} : Set (ℝ → ℝ → ℝ)), ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ y ∈ Set.Icc (y1 t) (y2 t), ∀ y' ∈ Set.Icc (y1 t) (y2 t),
        |G t y - G t y'| ≤ L * |y - y'|)
    -- (iv)
    (hc1 : MeasureTheory.IntegrableOn c1 (Set.Icc 0 T))
    (hc2 : MeasureTheory.IntegrableOn c2 (Set.Icc 0 T))
    (hC : ∀ α : ℝ → ℝ, Measurable α → (∀ s, |α s| ≤ L) → ∀ t ∈ Set.Icc (0 : ℝ) T,
      (∫ s in t..T, Real.exp (-∫ r in s..T, α r) * c1 s) ≤ C1 ∧
      (∫ s in t..T, Real.exp (-∫ r in s..T, α r) * c2 s) ≤ C2) :
    ∃ y0 : ℝ → ℝ, UnifiedFBSDE.Cubic.IsSolution F0 h0 T y0 ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, y1 t ≤ y0 t ∧ y0 t ≤ y2 t) ∧
      ∀ z : ℝ → ℝ, UnifiedFBSDE.Cubic.IsSolution F0 h0 T z →
        (∀ t ∈ Set.Icc (0 : ℝ) T, y1 t ≤ z t ∧ z t ≤ y2 t) →
        ∀ t ∈ Set.Icc (0 : ℝ) T, z t = y0 t := by sorry

end UnifiedFBSDE.Rational
