-- Prove2me | Theorems.Thm_UnaryQuadraticKKT_Hardness_normalization_dyadic
-- name    : UnaryQuadraticKKT.Hardness.normalization_dyadic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T15:45:50.400482+00:00
-- url     : https://prove2.me/theorems/1d8aece2-4cd0-463f-9ab3-8d301156a27c
-- title:
--   Lemma 4.2 — normalization and dyadic decomposition
-- statement:
--   Let $n\ge1$ and let $P$ be any rational quadratic of Equation (2), with the computed $A,M,L,\widetilde P$ above. Then
--   $$\operatorname{KKT}(P)=\operatorname{KKT}(\widetilde P).$$
--   For every coefficient slot $t$, its actual computed sign $s_t\in\{-1,+1\}$ and binary digits $\delta_{t,k}\in\{0,1\}$ satisfy
--   $$[t]\widetilde P=s_t\sum_{k=1}^L\delta_{t,k}2^{-k}.$$
--   This includes zero coefficients with sign $+1$ and all digits zero. The statement preserves both the entire real KKT set and every coefficient identity required for the source's dyadic expansion.
--
--   **Formalization Note** The public exact KKT predicate is used at all real points; normalization is computed, not supplied with a correctness hypothesis.
--
--   Differences from the source:
--   - encoding: the monomial convention of Equation (2) → the published objective ½xᵀQx+cᵀx with Q_ii=2q_ii and Q_ij=Q_ji=q_ij for i<j; reason: this invertible rational coefficient conversion preserves the entire polynomial and all its derivatives
--   - encoding: L=floor(log₂ M)+1 and an existential signed digit expansion → L is the bit length of M and the digits are the actual bits of the cleared coefficient magnitude; reason: M≥1 makes the lengths equal; this fixes the witness used in the source proof and covers every coefficient, including zero
-- source:
--   Argyrios Deligkas, Michail Fasoulakis, Stavros Ioannidis, STOC 2027 submission #1093 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1093.pdf, Lemma 4.2, Equation (4), p.5, proof continuing p.6. Canonical PDF SHA256 f4a6f774376cfc40e24acff39a11029782994f72d85350d10b69fc17030bd0a5

import Mathlib
import Definitions.Def_UnaryQuadraticKKT_Hardness_Normalization

set_option autoImplicit false

namespace UnaryQuadraticKKT.Hardness
open Finset NetworkEquilibriumCLS.LinearNash

/-- Lemma 4.2 and its actual binary digits, Eq. (4), pp.5–6. -/
theorem normalization_dyadic {n : ℕ} (hn : 0 < n) (p : Quadratic n) :
    (∀ x : Fin n → ℝ, QuadraticKKT p x ↔ QuadraticKKT (normalized p) x) ∧
    (∀ t ∈ slots n,
      (coefficientSign p t = -1 ∨ coefficientSign p t = 1) ∧
      (coefficient (normalized p) t : ℝ) = (coefficientSign p t : ℝ) *
        ∑ j : Fin (normalizationLength p),
          (if coefficientBit p t j then (1 : ℝ) else 0) *
            (2 : ℝ) ^ (-((j.val + 1 : ℕ) : ℤ))) := by sorry

end UnaryQuadraticKKT.Hardness
