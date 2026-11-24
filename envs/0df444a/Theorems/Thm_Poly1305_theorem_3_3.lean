-- Prove2me | Theorems.Thm_Poly1305_theorem_3_3
-- name    : Poly1305.theorem_3_3
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-24T07:43:53.177056+00:00
-- url     : https://prove2.me/theorems/9fdc2ed1-febe-4cd4-ba3c-cc31cbc1a21d
-- title:
--   Theorem 3.3 — at most 8⌈L/16⌉ values of r give H_r(m) = H_r(m′) + g
-- statement:
--   Bernstein, p. 8: “**Theorem 3.3.** Let $m, m'$ be distinct messages, each having at most $L$ bytes. Let $g$ be a 16-byte string. Let $R$ be a subset of $\{0, 1, \dots, 2^{130} - 6\}$. Then there are at most $8\lceil L/16\rceil$ integers $r \in R$ such that $H_r(m) = H_r(m') + g$.” And after the theorem: “Consequently, if $\#R = 2^{106}$, and if $r$ is a uniform random element of $R$, then $H_r(m) = H_r(m') + g$ with probability at most $8\lceil L/16\rceil/2^{106}$.”
--
--   The statement: for distinct messages $m \ne m'$ of at most $L$ bytes, a 16-byte string $g$, and a finite set $R$ of integers contained in $\{0, 1, \dots, 2^{130} - 6\}$, the number of $r \in R$ with $H_r(m) = H_r(m') + g$ (`H`, `add16`) is at most $8\lceil L/16\rceil$; and if $R$ has $2^{106}$ elements, then for $r$ drawn from the uniform distribution on $R$ (`PMF.uniformOfFinset`), the probability that $H_r(m) = H_r(m') + g$ is at most $8\lceil L/16\rceil/2^{106}$ (in `ENNReal`).
-- source:
--   Bernstein, D. J., The Poly1305-AES message-authentication code, in: Fast Software Encryption (FSE 2005), Lecture Notes in Computer Science 3557, Springer, 2005, 32–49, https://doi.org/10.1007/11502760_3 (author's version of 2005-03-29: https://cr.yp.to/mac/poly1305-20050329.pdf), p. 8, Theorem 3.3

import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Mathlib.Data.Rat.Floor
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Poly1305Bernstein

namespace Poly1305

theorem theorem_3_3 (m m' : Message) (hmm' : m ≠ m') (L : ℕ) (hm : m.length ≤ L)
    (hm' : m'.length ≤ L) (g : Str16) (R : Finset ℤ) (hR : R ⊆ Finset.Icc 0 (2 ^ 130 - 6)) :
    (R.filter (fun r => H r m = add16 (H r m') g)).card ≤ 8 * ⌈(L : ℚ) / 16⌉₊ ∧
    ∀ hR' : R.Nonempty, R.card = 2 ^ 106 →
      (PMF.uniformOfFinset R hR').toOuterMeasure {r | H r m = add16 (H r m') g} ≤
        (8 * ⌈(L : ℚ) / 16⌉₊ : ENNReal) / 2 ^ 106 := by
  sorry

end Poly1305
