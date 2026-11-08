-- Prove2me | Theorems.Thm_QuadraticRE_equation_1
-- name    : QuadraticRE.equation_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:11:14.400407+00:00
-- url     : https://prove2.me/theorems/37c2de9d-5c96-4c05-bb41-1a3bf962ea15
-- title:
--   Equation (1) — $\sum_i a_ic_i=ac$, with (3): $\sum_i y_i=abc+d$
-- statement:
--   For every depth $j\ge0$, all root bits $a,c$ and all masks $\theta_A,\theta_C$, the leaf shares $(a_i)=\mathrm{Sh}^j_A(a;\theta_A)$ and $(c_i)=\mathrm{Sh}^j_C(c;\theta_C)$ satisfy
--   $$\sum_{i=1}^{L}a_ic_i=ac .$$
--   Consequently, for every $h$, every input $(a,b,c,d)$ and every tape $R$ of $E_{j,h}$, the leaf bits satisfy $\sum_i y_i=abc+d$ (equation (3)).
--
--   This identity is what lets the decoder recover the cubic term from the leaves.
--
--   Differences from the source:
--   - generalization: equation (1) → equation (1) together with its consequence (3), Σ_i y_i = abc + d for every tape; reason: (3) is derived from (1) on p.19 and is the form the correctness proof uses; the first conjunct is (1) itself
-- source:
--   Orsini, Patra, From Degree Three to Degree Two: Statistical Randomized Encodings for All Functions, STOC 2027 submission manuscript (sha256 0c94deae…), eq. (1), p.16; eq. (3), p.19

import Mathlib
import Definitions.Def_QuadraticRE_encE

namespace QuadraticRE

/-- Equation (1) of Orsini, Patra, *From Degree Three to Degree Two*, STOC 2027 submission manuscript (sha256 0c94deae…), p.16, `∑_i a_i c_i = ac` for every choice of the masks, with its
corollary (3), p.19: `∑_i y_i = abc + d` for every tape. -/
theorem equation_1 (j : ℕ) :
    (∀ (a c : F2) (θA : Fin (maskLen .A j) → F2) (θC : Fin (maskLen .C j) → F2),
      ∑ i, Sh .A j a θA i * Sh .C j c θC i = a * c) ∧
    (∀ (h : ℕ) (a b c d : F2) (R : Tape j h), ∑ i, leafY a b c d R i = a * b * c + d) := by sorry

end QuadraticRE
