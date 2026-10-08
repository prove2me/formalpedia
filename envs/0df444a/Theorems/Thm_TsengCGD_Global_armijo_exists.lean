-- Prove2me | Theorems.Thm_TsengCGD_Global_armijo_exists
-- name    : TsengCGD.Global.armijo_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:54:50.610181+00:00
-- url     : https://prove2.me/theorems/d317c554-dfde-4b51-9399-7ee023918e3f
-- title:
--   §2 after (10) — negative descent quantity and Armijo trial existence
-- statement:
--   Under the standing assumptions, take $x\in\operatorname{dom}P$, a nonempty block $\mathcal J$, a positive-definite matrix $H$, and the exact direction $d$. Let $0<\beta,\sigma<1$, $0\le\gamma<1$, and let $a_0>0$ be an initial trial step. With $\Delta=\nabla f(x)^\top d+\gamma d^\top Hd+cP(x+d)-cP(x)$, the paper's claim after (10) includes
--
--   $$F_c(x+\alpha d)\le F_c(x)+\alpha\Delta+o(\alpha),\qquad
--   \Delta\le(\gamma-1)d^\top Hd<0\quad\text{if }d\ne0.$$
--
--   There is some $j\ge0$ for which $a_0\beta^j$ passes the Armijo test. This establishes that the backtracking rule has a positive accepted trial, including when $d=0$.
--
--   **Formalization Note** The little-$o$ remainder is explicit and the tested point must belong to $D$. The strict inequality is conditional on $d\ne0$; at $d=0$ a trial still exists.
-- source:
--   Tseng and Yun, A coordinate gradient descent method for nonsmooth separable minimization, Math. Program. Ser. B 117 (2009), p. 392, §2, claim after equation (10), https://doi.org/10.1007/s10107-007-0170-0

import Mathlib
import Definitions.Def_TsengCGD_Global_Basic

namespace TsengCGD.Global

open Filter Topology Finset Matrix
open scoped RealInnerProductSpace

theorem armijo_exists {n : ℕ} (f : Vec n → ℝ) (D : Set (Vec n)) (P : Vec n → ℝ)
    (c : ℝ) (hs : Standing f D P c)
    (x : Vec n) (hx : x ∈ D) (J : Finset (Fin n)) (hJ : J.Nonempty)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef)
    (d : Vec n) (hd : IsDir f D P c H x J d)
    (β σ γ a₀ : ℝ) (hparams : ArmijoParams β σ γ) (ha₀ : 0 < a₀) :
    (∃ r : ℝ → ℝ, Tendsto (fun a => r a / a) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      ∀ a ∈ Set.Ioc (0 : ℝ) 1,
        x + a • d ∈ D ∧
        Fc f P c (x + a • d) ≤ Fc f P c x + a * Delta f P c γ H x d + r a) ∧
    Delta f P c γ H x d ≤ (γ - 1) * qf H d ∧
    (d ≠ 0 → Delta f P c γ H x d < 0) ∧
    ∃ j : ℕ, ArmijoTest f D P c σ γ H x d (a₀ * β ^ j) := by sorry

end TsengCGD.Global
