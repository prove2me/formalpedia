-- Prove2me | Theorems.Thm_SaturatedNet_Uniqueness_proposition_4
-- name    : SaturatedNet.Uniqueness.proposition_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:44.856096+00:00
-- url     : https://prove2.me/theorems/44644969-7829-4fdd-a818-b5ea5e381128
-- title:
--   Proposition 4, p. 14 — if ρ(P) < 1, every exogenous flow gives a unique network equilibrium
-- statement:
--   Let $(P, w)$ be a network ($P \ge 0$, $w \ge 0$) with spectral radius $\rho(P) < 1$. Then for every
--   exogenous flow $c \in \mathbb R^n$ there is exactly one network equilibrium:
--
--   $$\exists!\, x \in \mathbb R^n:\quad x = S_0^w(P^\top x + c).$$
--
--   This is the asymptotically stable case of the uniqueness theory; in Theorem 2 it is applied to every
--   class whose block has spectral radius below one.
-- source:
--   Massai, Como & Fagnani, Equilibria and Systemic Risk in Saturated Networks, arXiv:1912.04815v2, p. 14, Proposition 4

import Mathlib
import Definitions.Def_SaturatedNet_Uniqueness_Model
open Matrix

namespace SaturatedNet.Uniqueness

theorem proposition_4 {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (w : n → ℝ) (hw : 0 ≤ w) (c : n → ℝ) (hρ : specRad P < 1) :
    ∃! x, IsEquilibrium P w c x := by sorry

end SaturatedNet.Uniqueness
