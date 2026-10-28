-- Prove2me | Theorems.Thm_PriceRobust_Stability_lemma_1
-- name    : PriceRobust.Stability.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:17:04.657137+00:00
-- url     : https://prove2.me/theorems/4485be5b-4575-4b85-82c7-817dbf39375b
-- title:
--   Lemma 1, p. 12 — the robust best response problem has a unique maximizer
-- statement:
--   Consider the market of §3 with $a\ge 0$ and Assumptions (P), (Z), (IS), and a cost vector $w\in\mathbb R^{\mathcal N}_{++}$. For every nonnegative price vector $p\ge 0$ there is exactly one vector $q$ that is a robust best response to $p$:
--   $$\exists!\,q:\quad q = RB(p),$$
--   i.e. for every firm $i$ the robust best response problem (7) over the feasible set (8), given $p_{-\mathcal N(i)}$, has a unique maximizer $q_{\mathcal N(i)}$.
--
--   This makes the robust best-response map $RB$ a well-defined function on $\mathbb R^{\mathcal N}_+$, so the dynamics $p^{n+1}=RB(p^n)$ are well posed.
--
--   **Formalization Note** The paper states the lemma firm by firm; since the firms' problems are independent, it is stated here jointly for all firms. The bundle of standing assumptions and $w>0$ is carried for uniformity with the other model statements.
-- source:
--   Federgruen & Hu, Global robust stability in a general price and assortment competition model, submitted manuscript (TSpace / SSRN 3010503), p. 12 (PDF 13), Lemma 1

import Mathlib
import Definitions.Def_PriceRobust_Stability_Model

open Matrix

namespace PriceRobust.Stability

theorem lemma_1 {ι F : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq F]
    (M : Market ι F) (hM : M.Standing) (w : ι → ℝ) (hw : ∀ l, 0 < w l)
    (p : ι → ℝ) (hp : 0 ≤ p) :
    ∃! q : ι → ℝ, M.IsRobustBR w p q := by sorry

end PriceRobust.Stability
