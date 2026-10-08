-- Prove2me | Theorems.Thm_VeinottSensitiveDP_Sensitive_lemma_7
-- name    : VeinottSensitiveDP.Sensitive.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:52:12.534679+00:00
-- url     : https://prove2.me/theorems/f2ed9e84-28f4-45e4-b91b-1c4022e89c3a
-- title:
--   Lemma 7 — for all small ρ > 0, P* + ρH is nonnegative, has positive diagonal, and is nonsingular
-- statement:
--   Let $P$ be an $S\times S$ substochastic matrix, $P^*$ the Cesàro limit of its powers and $H=(I-P+P^*)^{-1}-P^*$. There is $\rho_0>0$ such that for all $0<\rho<\rho_0$ the matrix
--   $$P^*+\rho H$$
--   has nonnegative entries, positive diagonal entries, and nonzero determinant.
--
--   The lemma lets the proofs of Theorems 4 and 5 compare Laurent coefficients without examining the chain structure of $P$.
--
--   **Formalization Note** "For all small enough $\rho>0$" is a statement eventually along $\rho\to0^+$.
-- source:
--   Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria, Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1644, §3, Lemma 7

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_VeinottSensitiveDP_Sensitive_Matrix
open Filter Topology Matrix BlackwellDiscreteDP.NearOne

namespace VeinottSensitiveDP.Sensitive

/-- Lemma 7: let `P` be an `S × S` substochastic matrix with `P* = limitMatrix P` and
`H = deviationMatrix P`. For all small enough `ρ > 0`, the matrix `P* + ρH` is non-negative,
has positive diagonal elements, and is nonsingular.

Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria,
Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1644, §3, Lemma 7.

**Formalization Note.** "For all small enough `ρ > 0`" is `∀ᶠ ρ in 𝓝[>] 0`; nonsingular is
`det ≠ 0`. -/
theorem lemma_7 {St : Type} [Fintype St] [DecidableEq St] (P : Matrix St St ℝ)
    (hP : IsSubstochastic P) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      (∀ i j, 0 ≤ (limitMatrix P + ρ • deviationMatrix P) i j) ∧
      (∀ i, 0 < (limitMatrix P + ρ • deviationMatrix P) i i) ∧
      (limitMatrix P + ρ • deviationMatrix P).det ≠ 0 := by sorry

end VeinottSensitiveDP.Sensitive
