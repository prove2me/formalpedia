-- Prove2me | Theorems.Thm_TsengCGD_Global_lemma1
-- name    : TsengCGD.Global.lemma1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:54:34.081899+00:00
-- url     : https://prove2.me/theorems/f45689c0-adc3-4622-a97a-1fa39a205f39
-- title:
--   Lemma 1 — descent estimate and quadratic-direction bound
-- statement:
--   Let $x\in\operatorname{dom}P$, let $\mathcal J$ be a nonempty coordinate set, and let $H$ be positive definite. If $d=d_H(x;\mathcal J)$ is the exact minimizer of the coordinate quadratic subproblem and $g=\nabla f(x)$, then, for $0<\alpha\le1$,
--
--   $$F_c(x+\alpha d)\le F_c(x)+\alpha\bigl(g^\top d+cP(x+d)-cP(x)\bigr)+o(\alpha),$$
--
--   and
--
--   $$g^\top d+cP(x+d)-cP(x)\le-d^\top Hd.$$
--
--   The first inequality relates the actual objective to the model direction; the second provides its quantitative descent bound.
--
--   **Formalization Note** The standing assumptions of (1) are explicit. The line segment $x+\alpha d$ belongs to $D$, so the displayed objective is finite. The remainder is a function $r(\alpha)$ with $r(\alpha)/\alpha\to0$ from the right; the statement holds for every exact minimizer.
-- source:
--   Tseng and Yun, A coordinate gradient descent method for nonsmooth separable minimization, Math. Program. Ser. B 117 (2009), p. 391, Lemma 1, equations (7)–(8), https://doi.org/10.1007/s10107-007-0170-0

import Mathlib
import Definitions.Def_TsengCGD_Global_Basic

namespace TsengCGD.Global

open Filter Topology Finset Matrix
open scoped RealInnerProductSpace

theorem lemma1 {n : ℕ} (f : Vec n → ℝ) (D : Set (Vec n)) (P : Vec n → ℝ)
    (c : ℝ) (hs : Standing f D P c)
    (x : Vec n) (hx : x ∈ D) (J : Finset (Fin n)) (hJ : J.Nonempty)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef)
    (d : Vec n) (hd : IsDir f D P c H x J d) :
    (∃ r : ℝ → ℝ, Tendsto (fun a => r a / a) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      ∀ a ∈ Set.Ioc (0 : ℝ) 1,
        x + a • d ∈ D ∧
        Fc f P c (x + a • d) ≤
          Fc f P c x + a * (⟪gradient f x, d⟫ + c * P (x + d) - c * P x) + r a) ∧
    ⟪gradient f x, d⟫ + c * P (x + d) - c * P x ≤ -qf H d := by sorry

end TsengCGD.Global
