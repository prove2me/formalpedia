-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P35_duality
-- name    : QAlgorithms.Papers.Independent.Dependency50.P35.duality
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:06:09.630078+00:00
-- url     : https://prove2.me/theorems/61a4cf5e-98b8-4463-8b72-cf779d447ec1
-- title:
--   Theorem 10 (Duality)
-- statement:
--   Let $\alpha,\beta\in(1/2,1)\cup(1,\infty)$ satisfy $1/\alpha+1/\beta=2$. Let $\rho_{ABC}=|\psi\rangle\langle\psi|$ for a unit vector $\psi$, so that the state is pure and normalized. With $\rho_{AB}=\operatorname{Tr}_C\rho_{ABC}$ and $\rho_{AC}=\operatorname{Tr}_B\rho_{ABC}$,
--
--   $$
--   \widetilde H_\alpha(A|B)_{\rho_{AB}}=-\widetilde H_\beta(A|C)_{\rho_{AC}}.
--   $$
--
--   The second entropy has order $\beta$, as in Theorem 10 and its proof, correcting the introductory bullet's repeated $\alpha$. This is the conditional-entropy duality for finite orders strictly above one half.
-- source:
--   On quantum Renyi entropies: a new generalization and some properties, arXiv:1306.3142v4, PDF p. 13, Theorem 10 (Duality)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Dependency50.P35

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted matrix type and positive-operator Schatten expression.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat schatten)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

/-- PDF p.13, Theorem 10: the second order is beta (the p.2 bullet has a typo).
A normalized pure-vector witness is explicit. -/
theorem duality {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (a b : ℝ) (ha : (1/2 : ℝ) < a ∧ a ≠ 1) (hb : (1/2 : ℝ) < b ∧ b ≠ 1)
    (hab : 1/a + 1/b = 2) (rho : Mat (A × (B × C))) (hr : Density rho)
    (hpure : ∃ psi : A × (B × C) → ℂ,
      (∑ i, Complex.normSq (psi i)) = 1 ∧ ∀ i j, rho i j = psi i * conj (psi j)) :
    conditionalRenyi a (marginalAB rho) = -conditionalRenyi b (marginalAC rho) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P35

end
