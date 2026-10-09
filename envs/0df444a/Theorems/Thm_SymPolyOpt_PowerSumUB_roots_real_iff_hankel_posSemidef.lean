-- Prove2me | Theorems.Thm_SymPolyOpt_PowerSumUB_roots_real_iff_hankel_posSemidef
-- name    : SymPolyOpt.PowerSumUB.roots_real_iff_hankel_posSemidef
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:22:40.070118+00:00
-- url     : https://prove2.me/theorems/dbd54a3f-109b-4b7d-86f8-ec9cc401963c
-- title:
--   §6.2, p. 26 — all roots of p are real iff H_m(s) ⪰ 0 (Hermite's criterion)
-- statement:
--   Let $p$ be a monic real polynomial of degree $m$ with Newton sums $s_k = \sum_z z^k$ (over its complex roots with multiplicity, so $s_0 = m$), and let $H_m(s) = (s_{i+j-2})_{1 \le i,j \le m}$ be its Hankel matrix. Then
--   $$\text{all roots of } p \text{ are real} \iff H_m(s) \succeq 0.$$
--
--   This classical criterion, due to Hermite and Sylvester, is what lets the SDP (6.7) encode the real-rootedness of the polynomial whose roots are a candidate solution of (6.4).
-- source:
--   Riener, Theobald, Jansson Andrén and Lasserre, Exploiting symmetries in SDP-relaxations for polynomial optimization, arXiv:1103.0486v3, p. 26, §6.2, "A necessary and sufficient condition for all roots of p to be real is that H_m(s) ⪰ 0"

import Mathlib
import Definitions.Def_SymPolyOpt_PowerSumUB_Setting

namespace SymPolyOpt.PowerSumUB

open Polynomial

theorem roots_real_iff_hankel_posSemidef (m : ℕ) (p : ℝ[X]) (hp : p.Monic)
    (hdeg : p.natDegree = m) :
    (∀ z ∈ p.aroots ℂ, z.im = 0) ↔ (SymPolyOpt.PowerSumLB.hankel m (newtonSum p)).PosSemidef := by sorry

end SymPolyOpt.PowerSumUB
