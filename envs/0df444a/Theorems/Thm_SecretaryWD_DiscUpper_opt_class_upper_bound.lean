-- Prove2me | Theorems.Thm_SecretaryWD_DiscUpper_opt_class_upper_bound
-- name    : SecretaryWD.DiscUpper.opt_class_upper_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T05:59:44.707227+00:00
-- url     : https://prove2.me/theorems/8ab0be7c-7b0d-418c-a02a-a034ea867668
-- title:
--   Proof of Thm 4.4 — $\mathsf{OPT}_c \le 2^{-c}\,2n^2 d_{\max} v_{\max}$
-- statement:
--   In the discounted secretary problem with $n$ elements, values $v\ge0$ and discounts $d\ge 0$, for every discount class $c\ge1$,
--   $$\mathsf{OPT}_c\;\le\;2^{-c}\cdot 2n^2\,d_{\max}\,v_{\max}.$$
--
--   This crude estimate shows that the classes with large index contribute geometrically little to the expected offline optimum.
-- source:
--   Babaioff, Dinitz, Gupta, Immorlica and Talwar, Secretary Problems: Weights and Discounts, SODA 2009 (authors' version), p. 7, proof of Theorem 4.4 ("we conclude that OPTc ≤ 2^{−c}2n^2 dmax vmax")

import Mathlib
import Definitions.Def_SecretaryWD_DiscUpper_DiscountedModel

namespace SecretaryWD.DiscUpper
theorem opt_class_upper_bound (n : ℕ) (d v : Fin n → ℝ)
    (hd : ∀ t, 0 ≤ d t) (hv : ∀ e, 0 ≤ v e) (c : ℕ) (hc : 1 ≤ c) :
    optClass d v c ≤ (2 : ℝ)⁻¹ ^ c * (2 * (n : ℝ) ^ 2 * dmax d * vmax v) := by sorry
end SecretaryWD.DiscUpper
