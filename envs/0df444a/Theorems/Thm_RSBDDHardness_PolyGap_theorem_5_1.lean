-- Prove2me | Theorems.Thm_RSBDDHardness_PolyGap_theorem_5_1
-- name    : RSBDDHardness.PolyGap.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:27:00.284762+00:00
-- url     : https://prove2.me/theorems/0e707f97-d9d8-45da-a76a-da90208bc013
-- title:
--   Theorem 5.1 — elementary point-count bounds for moment fibers
-- statement:
--   Let $q$ be prime, $2\le d<q$ and $h\ge2d+2$. For $c\in\mathbb F_q^d$ let
--   $$X_{c,h}=\Bigl\{x\in\mathbb F_q^h:\sum_{i=1}^h x_i^j=c_j,\ 1\le j\le d\Bigr\},$$
--   $Z_r=X_{c,h}\cap\{x_r=0\}$ and $Y_{r,s}=X_{c,h}\cap\{x_r=x_s\}$. Then, uniformly for every $c$,
--
--   1. $\bigl||X_{c,h}|-q^{h-d}\bigr|\le d!\,(d-1)^{h-2d}\,q^{h/2}$ (13);
--   2. for every $r$, $\bigl||Z_r|-q^{h-d-1}\bigr|\le d!\,(d-1)^{h-2d-1}\,q^{(h-1)/2}$ (14);
--   3. for every $r\ne s$, $\bigl||Y_{r,s}|-q^{h-d-1}\bigr|\le d!\,(d-1)^{h-2d-1}\,q^{(h-1)/2}$ (15).
--
--   These estimates are the arithmetic input to the completion theorem (Theorem 5.2): they show that the moment fibers are nonempty and contain tuples of distinct nonzero coordinates.
--
--   Differences from the source:
--   - encoding: indexed targets c_1, …, c_d (or r_1, …, r_d) → a function on ℕ of which only the values at 1, …, d are used; reason: same instances; avoids Fin-indexed casts
--   - encoding: cardinalities |X|, |Z_r|, |Y_{r,s}| and powers q^{h/2}, q^{(h-1)/2} → Set.ncard of finite sets of functions Fin h → ZMod q, real powers of q; reason: the sets are finite since q is prime; the real powers are the source exponents
--   - encoding: coordinates x_1..x_h, indices r, s ∈ {1..h} → Fin h (0-based); reason: renaming only
-- source:
--   Daqing Wan, Jun Zhang, NP-Hardness of Bounded Distance Decoding for Reed–Solomon Codes, STOC 2027 submission #449 (October 2026), Theorem 5.1, eqs. (13)–(15); definitions of X_{c,h}, Y_{r,s}, Z_r in §5.1, PDF pp. 14–15, PDF p. 15 (printed p. 14); PDF SHA-256 d60d9a54b73aa972494f130439dc6e07f8c7b33556741f8324d22cf45218e22b

import Mathlib
import Definitions.Def_RSBDDHardness_PolyGap_Algebra
set_option autoImplicit false
open scoped BigOperators
open Classical

namespace RSBDDHardness.PolyGap

/-- Theorem 5.1 (Elementary point-count bounds), PDF 15. Let `q` be prime, `2 ≤ d < q`,
`h ≥ 2d + 2`. Uniformly for every `c ∈ 𝔽_q^d`, (13) `||X_{c,h}| − q^{h−d}| ≤ d!(d−1)^{h−2d} q^{h/2}`,
and for every `r` (14) and every `r ≠ s` (15) the sets `Z_r`, `Y_{r,s}` satisfy
`||·| − q^{h−d−1}| ≤ d!(d−1)^{h−2d−1} q^{(h−1)/2}`. -/
theorem theorem_5_1 (q d h : ℕ) (hq : q.Prime) (hd : 2 ≤ d) (hdq : d < q) (hh : 2 * d + 2 ≤ h)
    (c : ℕ → ZMod q) :
    |((Xfib q h d c).ncard : ℝ) - (q : ℝ) ^ (h - d)| ≤
        (d.factorial : ℝ) * ((d : ℝ) - 1) ^ (h - 2 * d) * (q : ℝ) ^ ((h : ℝ) / 2) ∧
      (∀ r : Fin h, |((Zfib q h d c r).ncard : ℝ) - (q : ℝ) ^ (h - d - 1)| ≤
        (d.factorial : ℝ) * ((d : ℝ) - 1) ^ (h - 2 * d - 1) * (q : ℝ) ^ (((h : ℝ) - 1) / 2)) ∧
      (∀ r s : Fin h, r ≠ s → |((Yfib q h d c r s).ncard : ℝ) - (q : ℝ) ^ (h - d - 1)| ≤
        (d.factorial : ℝ) * ((d : ℝ) - 1) ^ (h - 2 * d - 1) * (q : ℝ) ^ (((h : ℝ) - 1) / 2)) := by sorry

end RSBDDHardness.PolyGap
