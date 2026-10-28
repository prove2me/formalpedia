-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_hermitian_parity
-- name    : QAlgorithms.Papers.Independent.Information100.P19.hermitian_parity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:40:29.725168+00:00
-- url     : https://prove2.me/theorems/54fe44c4-b427-471f-a109-6d6d13f9aeb8
-- title:
--   Proposition 2.2
-- statement:
--   Let $n\ge1$ and let $I_n^{\rm all}$ be the dimension-free cone of formal power-sum inequalities on Hermitian matrices. Then
--   $$n\text{ odd}\implies I_n^{\rm all}=\{0\}.$$
--   For even $n$, every partition monomial whose parts are even belongs to this cone; in particular $[2m]\in I_{2m}^{\rm all}$ for $m\ge1$. Zero matrices are included. These assertions distinguish parity positivity from dimension-dependent trace identities.
--
--   For a partition $\lambda$, the symbol $[\lambda]$ denotes a formal basis element evaluated as $\prod_j\operatorname{Tr}(X^{\lambda_j})$. Distinct formal coefficients are not identified by any fixed-dimensional trace identity.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 9, Proposition 2.2

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- Proposition 2.2; arXiv:2609.29471v1, PDF pp.9. -/
theorem hermitian_parity (n : ℕ) (hn : 1 ≤ n) :
    (Odd n → allCone n = {0}) ∧
    (Even n → ∀ l : Part n, (∀ k ∈ l.val, Even k) → Finsupp.single l 1 ∈ allCone n) ∧
    (∀ m : ℕ, 1 ≤ m → ∀ l : Part (2*m), l.val = [2*m] →
      Finsupp.single l 1 ∈ allCone (2*m)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
