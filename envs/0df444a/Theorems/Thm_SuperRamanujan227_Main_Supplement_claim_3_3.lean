-- Prove2me | Theorems.Thm_SuperRamanujan227_Main_Supplement_claim_3_3
-- name    : SuperRamanujan227.Main.Supplement.claim_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:45:53.394211+00:00
-- url     : https://prove2.me/theorems/f721385c-ebae-4c62-bc96-36e3cae2b880
-- title:
--   Claim 3.3 — Exact matching inverse-transform difference
-- statement:
--   Let $n$ be even and $3\le d<n$. For a perfect matching $M$ on $n$ vertices put $p_M=\chi_M/(x-1)$ and $y_0=\sqrt{d-1}/(d-2)$. Using the same normalized Cauchy transform and its right inverse, define $\eta=4(d-2)\sqrt{d-1}/(d^2(n-1))$. Then
--
--   $$K_{\chi_M}(y_0)-K_{p_M}(y_0)=\frac{d\bigl(1-\sqrt{1-\eta}\bigr)}{2\sqrt{d-1}}.$$
--
--   The exact equality, including its radicand, supplies the quantitative gain used with Claim 3.2. It is a conclusion about the independently defined inverse; it is not a defining formula or an inverse-existence hypothesis.
--
--   Differences from the source:
--   - encoding: a fixed perfect matching M on even n vertices → its characteristic polynomial (x-1)^(n/2)(x+1)^(n/2), with one factor x-1 deleted for p_M; reason: every such matching has exactly this characteristic polynomial; no matching or root multiplicity is restricted
-- source:
--   Gil Cohen, Gal Maor, STOC 2027 submission #227 (October 2026), p. 11, Claim 3.3

import Mathlib
import Definitions.Def_SuperRamanujan227_Main_Supplement_Transforms

namespace SuperRamanujan227.Main.Supplement

/-- Claim 3.3, Eq. (15), p.11; eta is the independently defined exact expression. -/
theorem claim_3_3 (n d : ℕ) (hn : Even n) (hd : 3 ≤ d) (hdn : d < n) :
    inverseCauchy (matchingChar n) (yZero d) -
      inverseCauchy (reducedMatching n) (yZero d) =
        (d : ℝ) * (1 - Real.sqrt (1 - eta n d)) / (2 * Real.sqrt ((d : ℝ) - 1)) := by sorry

end SuperRamanujan227.Main.Supplement
