-- Prove2me | Theorems.Thm_RevRedSAT_lemma_B_7
-- name    : RevRedSAT.lemma_B_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:47:28.02868+00:00
-- url     : https://prove2.me/theorems/f9b55d6c-c2d6-4e70-941b-2fb6b8903f68
-- title:
--   Lemma B.7 — the branching inequality $2^{-\delta\Delta_C}+2^{-\delta\Delta_P}\le1$
-- statement:
--   Let $d\ge2$, $\delta=2^{-j}$ with $j\ge2$, $s\le d$, a petal size $1\le p<s$ and the core size $c=s-p$. With $\Delta_C=w_c/2$ and $\Delta_P=w_pt_p/2$,
--
--   $$2^{-\delta\Delta_C}+2^{-\delta\Delta_P}\le1.$$
--
--   The inequality bounds the number of leaves of the sparsification recursion by $2^{\delta k}$.
--
--   Differences from the source:
--   - encoding: δ = 2^{−j}, weights and thresholds (17) → j : ℕ; real powers of 2; reason: same quantities
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma B.7, p.90 (printed) = PDF p.92

import Mathlib
import Definitions.Def_RevRedSAT_mu

set_option autoImplicit false

namespace RevRedSAT

/-- **Lemma B.7 (the branching inequality).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma B.7, p.90: "For the decreases ∆C and ∆P in Lemma B.6, 2^{−δ∆C} + 2^{−δ∆P} ≤ 1."

With `δ = 2^{−j}`, `j ≥ 2`, `d ≥ 2`, a layer `s ≤ d`, petal size `1 ≤ p < s` and core size
`c = s − p`: `∆C = w_c/2`, `∆P = w_p t_p/2`, and `2^{−δ∆C} + 2^{−δ∆P} ≤ 1`.

**Formalization Note** Real powers of `2` (`Real.rpow`). -/
theorem lemma_B_7 (d j s p : ℕ) (hd : 2 ≤ d) (hj : 2 ≤ j) (hp : 1 ≤ p) (hps : p < s)
    (hs : s ≤ d) :
    (2 : ℝ) ^ (-(deltaOf j * (ws d j (s - p) / 2))) +
      (2 : ℝ) ^ (-(deltaOf j * (ws d j p * tp d j p / 2))) ≤ 1 := by sorry

end RevRedSAT
