-- Prove2me | Theorems.Thm_Section5PowerCode_sum_powers_ne_zero
-- name    : Section5PowerCode.sum_powers_ne_zero
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:39:13.22403+00:00
-- url     : https://prove2.me/theorems/c2c5859a-cdaf-5214-9016-98f59b80851b
-- title:
--   An injective tuple has a nonzero power sum
-- statement:
--   Let $F$ be any field, $1\le m\le k$, and let $v_1,\ldots,v_m\in F$ be pairwise distinct. Then
--
--   $$\exists j\in\{0,\ldots,k-1\}:\quad\sum_{i=1}^m v_i^j
--   e0.$$
--
--   This is a nondegeneracy property used to construct bounded-independence power codes.
-- source:
--   Original auxiliary result for Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5 (formalization support, not an assertion that the paper states this auxiliary lemma verbatim). Exact formalization: Solutions/Section5PowerCode.lean, lines 11–22.

import Mathlib
set_option autoImplicit false
namespace Section5PowerCode
end Section5PowerCode
open Section5PowerCode

theorem Section5PowerCode.sum_powers_ne_zero {F : Type*} [Field F] {m k : ℕ}
    (hm : 0 < m) (hk : m ≤ k) (v : Fin m → F) (hv : Function.Injective v) :
    ∃ j : Fin k, (∑ i, v i ^ (j : ℕ)) ≠ 0 := by sorry
