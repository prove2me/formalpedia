-- Prove2me | Theorems.Thm_TsengCGD_Global_lemma2
-- name    : TsengCGD.Global.lemma2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:54:45.950711+00:00
-- url     : https://prove2.me/theorems/6a78601b-ae06-4568-9f11-794552fbc8da
-- title:
--   Lemma 2 — stationarity exactly when the full direction vanishes
-- statement:
--   Let $x\in\operatorname{dom}P$ and let $H$ be positive definite. The full-coordinate quadratic direction $d_H(x)=d_H(x;\mathcal N)$ vanishes precisely at stationary points of $F_c$:
--
--   $$F_c'(x;v)\ge0\ \text{for every }v\in\mathbb R^n
--   \quad\Longleftrightarrow\quad d_H(x)=0.$$
--
--   This characterization turns a variational first-order condition into a residual test for the exact subproblem.
--
--   **Formalization Note** Stationarity includes $x\in D$ and uses the one-sided derivative of the extended-valued objective. The Lean predicate uses the equivalent nonnegative lower-limit condition; directions leaving $D$ have value $+\infty$. The standing assumptions of (1) are explicit.
-- source:
--   Tseng and Yun, A coordinate gradient descent method for nonsmooth separable minimization, Math. Program. Ser. B 117 (2009), p. 394, Lemma 2, https://doi.org/10.1007/s10107-007-0170-0

import Mathlib
import Definitions.Def_TsengCGD_Global_Basic

namespace TsengCGD.Global

open Filter Topology Finset Matrix
open scoped RealInnerProductSpace

theorem lemma2 {n : ℕ} (f : Vec n → ℝ) (D : Set (Vec n)) (P : Vec n → ℝ)
    (c : ℝ) (hs : Standing f D P c)
    (x : Vec n) (hx : x ∈ D) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef) :
    IsStationary f D P c x ↔ dH f D P c H x Finset.univ = 0 := by sorry

end TsengCGD.Global
