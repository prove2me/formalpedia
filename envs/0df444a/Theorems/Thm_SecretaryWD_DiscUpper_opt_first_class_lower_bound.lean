-- Prove2me | Theorems.Thm_SecretaryWD_DiscUpper_opt_first_class_lower_bound
-- name    : SecretaryWD.DiscUpper.opt_first_class_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T05:59:25.164531+00:00
-- url     : https://prove2.me/theorems/c2e17c7b-5c55-4939-bb62-5bb26579c3c8
-- title:
--   Proof of Thm 4.4 — $\mathsf{OPT}_1 \ge v_{\max} d_{\max}/n$
-- statement:
--   In the discounted secretary problem with $n\ge1$ elements, values $v\ge 0$ and discounts $d\ge0$, the part of the expected offline optimum earned in the top discount class $P_1=\{i: d(i)\in(d_{\max}/2, d_{\max}]\}$ satisfies
--   $$\mathsf{OPT}_1\;\ge\;\frac{v_{\max}\,d_{\max}}{n}.$$
--
--   It gives the lower bound on $\mathbb E_\pi[\mathsf{OPT}]$ against which the low discount classes are shown to be negligible.
-- source:
--   Babaioff, Dinitz, Gupta, Immorlica and Talwar, Secretary Problems: Weights and Discounts, SODA 2009 (authors' version), p. 7, proof of Theorem 4.4 ("Clearly OPT1 ≥ vmaxdmax/n")

import Mathlib
import Definitions.Def_SecretaryWD_DiscUpper_DiscountedModel

namespace SecretaryWD.DiscUpper
theorem opt_first_class_lower_bound (n : ℕ) (hn : 1 ≤ n) (d v : Fin n → ℝ)
    (hd : ∀ t, 0 ≤ d t) (hv : ∀ e, 0 ≤ v e) :
    vmax v * dmax d / n ≤ optClass d v 1 := by sorry
end SecretaryWD.DiscUpper
