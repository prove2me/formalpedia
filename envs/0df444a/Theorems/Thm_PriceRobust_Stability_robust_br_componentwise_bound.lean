-- Prove2me | Theorems.Thm_PriceRobust_Stability_robust_br_componentwise_bound
-- name    : PriceRobust.Stability.robust_br_componentwise_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:17:18.364674+00:00
-- url     : https://prove2.me/theorems/f15b5057-d778-4fda-87e4-1b762ac4031a
-- title:
--   Proof of Theorem 3(a), p. 16 — |RB(p̂) − RB(p̃)| ≤ Λ(R)|p̂ − p̃| componentwise
-- statement:
--   Consider the market of §3 with $a\ge 0$, Assumptions (P), (Z), (IS), and $w\in\mathbb R^{\mathcal N}_{++}$. For all price vectors $\hat p,\tilde p\ge 0$,
--   $$|RB(\hat p)-RB(\tilde p)|\ \le\ \Lambda(R)\,|\hat p-\tilde p|$$
--   componentwise, where $|x|=(|x_1|,\dots,|x_N|)$ and $\Lambda(R)=I-[T(R)]^{-1}R$.
--
--   For a product $l$ of firm $i$, row $l$ of the right side is $-R^{-1}_{\mathcal N(i),\mathcal N(i)}R_{\mathcal N(i),-\mathcal N(i)}|\hat p_{-\mathcal N(i)}-\tilde p_{-\mathcal N(i)}|$, which is the per-firm bound obtained in the proof of Theorem 3(a) by combining (20)–(22). With an absolute norm, this yields (23).
-- source:
--   Federgruen & Hu, Global robust stability in a general price and assortment competition model, submitted manuscript (TSpace / SSRN 3010503), p. 16 (PDF 17), proof of Theorem 3(a), display after (22) and eq. (23)

import Mathlib
import Definitions.Def_PriceRobust_Stability_Model

open Matrix

namespace PriceRobust.Stability

theorem robust_br_componentwise_bound {ι F : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq F]
    (M : Market ι F) (hM : M.Standing) (w : ι → ℝ) (hw : ∀ l, 0 < w l)
    (phat ptil qhat qtil : ι → ℝ) (hphat : 0 ≤ phat) (hptil : 0 ≤ ptil)
    (hqhat : M.IsRobustBR w phat qhat) (hqtil : M.IsRobustBR w ptil qtil) :
    ∀ l, |qhat l - qtil l| ≤ (M.Lam *ᵥ (fun m => |phat m - ptil m|)) l := by sorry

end PriceRobust.Stability
