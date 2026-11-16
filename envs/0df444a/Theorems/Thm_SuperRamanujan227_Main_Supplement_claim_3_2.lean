-- Prove2me | Theorems.Thm_SuperRamanujan227_Main_Supplement_claim_3_2
-- name    : SuperRamanujan227.Main.Supplement.claim_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:45:20.157259+00:00
-- url     : https://prove2.me/theorems/3633e69b-56bb-41ea-8dba-a16863570209
-- title:
--   Claim 3.2 — Convolution inverse-transform improvement
-- statement:
--   Let $n$ be even and $3\le d<n$. Let $M$ be any fixed perfect-matching adjacency on $n$ vertices, $p_M=\chi_M/(x-1)$, and $y_0=\sqrt{d-1}/(d-2)$. Write $K$ for the right inverse of the normalized empirical-root Cauchy transform and use finite free additive convolution in degree $n-1$. Then
--
--   $$K_{p_M^{\boxplus d}}(y_0)\le2\sqrt{d-1}-d\bigl(K_{\chi_M}(y_0)-K_{p_M}(y_0)\bigr).$$
--
--   This is the paper's retained inverse-transform gain supporting Theorem 3.1. The matching characteristic polynomial, reduced polynomial, convolution and inverse are defined independently of the inequality.
--
--   Differences from the source:
--   - encoding: a fixed perfect matching M on even n vertices → its characteristic polynomial (x-1)^(n/2)(x+1)^(n/2), with one factor x-1 deleted for p_M; reason: every such matching has exactly this characteristic polynomial; no matching or root multiplicity is restricted
-- source:
--   Gil Cohen, Gal Maor, STOC 2027 submission #227 (October 2026), p. 11, Claim 3.2

import Mathlib
import Definitions.Def_SuperRamanujan227_Main_Supplement_Transforms

namespace SuperRamanujan227.Main.Supplement

/-- Claim 3.2, p.11, with the inherited matching, y₀ and degree n-1 convolution. -/
theorem claim_3_2 (n d : ℕ) (hn : Even n) (hd : 3 ≤ d) (hdn : d < n) :
    inverseCauchy (matchingConvolution n d) (yZero d) ≤
      2 * Real.sqrt ((d : ℝ) - 1) - (d : ℝ) *
        (inverseCauchy (matchingChar n) (yZero d) -
          inverseCauchy (reducedMatching n) (yZero d)) := by sorry

end SuperRamanujan227.Main.Supplement
