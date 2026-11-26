-- Prove2me | Theorems.Thm_Section5PowerCode_codeSign_product_sum_zero
-- name    : Section5PowerCode.codeSign_product_sum_zero
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:44:50.518629+00:00
-- url     : https://prove2.me/theorems/82404c4f-06f8-5134-b834-7517b4b5802b
-- title:
--   Vanishing products of power-code characters
-- statement:
--   Let $F$ be a finite field, $\chi:(F,+)\to(\mathbb R,\times)$ a nontrivial additive character, and $v:I\to F$ injective. For seeds $t\in F^k$, define $s_i(t)=\chi(\sum_{j=0}^{k-1}t_jv(i)^j)$. If $S\subset I$ is finite, nonempty, and $|S|\le k$, then
--
--   $$\sum_{t\in F^k}\prod_{i\in S}s_i(t)=0.$$
--
--   This establishes the mixed-product cancellation needed for moment matching; characteristic two is not required in this declaration.
-- source:
--   Original auxiliary result for Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5 (formalization support, not an assertion that the paper states this auxiliary lemma verbatim). Exact formalization: Solutions/Section5PowerCodeCharacters.lean, lines 65–70.

import Definitions.Def_Section5Verified_Section5PowerCodeCharacters
import Mathlib
import Theorems.Thm_Section5PowerCode_sum_powers_ne_zero
set_option autoImplicit false
namespace Section5PowerCode
end Section5PowerCode
open Section5PowerCode
variable {F : Type*} [Field F] [Fintype F]

theorem Section5PowerCode.codeSign_product_sum_zero {ι : Type*} [DecidableEq ι] {k : ℕ}
    (χ : AddChar F ℝ) (hχ : χ ≠ 0) (v : ι → F) (hv : Function.Injective v)
    (S : Finset ι) (hS : S.Nonempty) (hk : S.card ≤ k) :
    (∑ t : Fin k → F, ∏ i ∈ S, Section5PowerCode.codeSign χ v t i)=0 := by sorry
