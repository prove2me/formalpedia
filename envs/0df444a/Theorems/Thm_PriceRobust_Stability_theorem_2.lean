-- Prove2me | Theorems.Thm_PriceRobust_Stability_theorem_2
-- name    : PriceRobust.Stability.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:17:19.36832+00:00
-- url     : https://prove2.me/theorems/52172895-e6cd-4a40-ad37-f332604bc84a
-- title:
--   Theorem 2, p. 13 — the special equilibrium (p*|w) is a fixed point of the robust best response map
-- statement:
--   Consider the market of §3 with $a\ge 0$ and Assumptions (P), (Z), (IS). Fix $w\in\mathbb R^{\mathcal N}_{++}$ and let $w'$ solve the cost-projection LCP (12)–(14). Then the special equilibrium
--   $$(p^*|w) = w' + [R+T(R)]^{-1}(a-Rw')$$
--   is a fixed point of the robust best response map:
--   $$RB\big((p^*|w)\big) = (p^*|w).$$
--
--   In particular $(p^*|w)$ is feasible for every firm's robust problem: it is nonnegative and its affine demands are nonnegative. Together with the contraction property (Theorem 3(a)) this identifies $(p^*|w)$ as the limit of the robust best-response dynamics.
--
--   **Formalization Note** "$RB(p)=p$" is stated as: $p$ is a robust best response to itself, for every firm. The proof in the paper relies on Propositions 2(a), 2(b) of Federgruen and Hu (2015) and Theorem 1(d) of this paper.
-- source:
--   Federgruen & Hu, Global robust stability in a general price and assortment competition model, submitted manuscript (TSpace / SSRN 3010503), p. 13 (PDF 14), Theorem 2

import Mathlib
import Definitions.Def_PriceRobust_Stability_Model

open Matrix

namespace PriceRobust.Stability

theorem theorem_2 {ι F : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq F]
    (M : Market ι F) (hM : M.Standing) (w : ι → ℝ) (hw : ∀ l, 0 < w l)
    (w' : ι → ℝ) (hw' : M.IsCostProjection w w') :
    M.IsRobustBR w (M.pstar w') (M.pstar w') := by sorry

end PriceRobust.Stability
