-- Prove2me | Theorems.Thm_TsengBCD_Stationary_stationary_of_coordMin_of_regular
-- name    : TsengBCD.Stationary.stationary_of_coordMin_of_regular
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T22:17:55.197235+00:00
-- url     : https://prove2.me/theorems/5bac04aa-4386-45b8-b51c-8255146c41b2
-- title:
--   §3, p. 479, remark after (5) — a coordinatewise minimum point at which f is regular is stationary
-- statement:
--   Let $f:\mathbb R^{n_1+\cdots+n_N}\to\mathbb R\cup\{\infty\}$ and let $z$ be a coordinatewise minimum point of $f$, i.e. $z\in\operatorname{dom}f$ and $f(z+(0,\dots,d_k,\dots,0))\ge f(z)$ for all $d_k$ and all $k$ (4). If $f$ is regular at $z$ in the sense of (5), then $z$ is a stationary point of $f$:
--   $$f'(z;d)\ge 0\qquad\text{for all } d.$$
--
--   The step is that (4) gives $f'(z;(0,\dots,d_k,\dots,0))\ge 0$ for every block, and regularity turns these blockwise inequalities into stationarity. It is the last step of each part of Theorem 4.1.
--
--   **Formalization Note.** Directional derivatives are lower limits in `EReal`. The hypothesis that $f$ never takes the value $-\infty$ is the paper's standing assumption $f:\mathbb R^{n_1+\cdots+n_N}\to\mathbb R\cup\{\infty\}$ (§1); it is needed, since for $f\equiv-\infty$ every point is a coordinatewise minimum point at which $f$ is (vacuously) regular, while every difference quotient is $-\infty-(-\infty)=-\infty$ in `EReal`.
-- source:
--   Tseng, Convergence of a block coordinate descent method for nondifferentiable minimization, J. Optim. Theory Appl. 109 (2001), p. 479, §3, remark after (5)

import Mathlib
import Definitions.Def_TsengBCD_Stationary_Setting

namespace TsengBCD.Stationary

open Filter Topology

theorem stationary_of_coordMin_of_regular {N : ℕ} {n : Fin N → ℕ} (f : X n → EReal)
    (hbot : ∀ x, f x ≠ ⊥) (z : X n) :
    IsCoordMin f z → IsRegularAt f z → IsStationary f z := by sorry

end TsengBCD.Stationary
