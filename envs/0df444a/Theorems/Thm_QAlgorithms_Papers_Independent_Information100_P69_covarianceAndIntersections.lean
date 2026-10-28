-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P69_covarianceAndIntersections
-- name    : QAlgorithms.Papers.Independent.Information100.P69.covarianceAndIntersections
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:05:31.722358+00:00
-- url     : https://prove2.me/theorems/ad496e2a-030b-4846-baf5-3555faddb022
-- title:
--   Covariance and intersections
-- statement:
--   Let $G$ be any group with finite-dimensional unitary representations $U_A,U_B$, and let $\tau,\omega$ be faithful invariant density matrices. The full channel family defined by
--   $$M\circ\operatorname{Ad}_{U_A(g)^{\otimes n}}=\operatorname{Ad}_{U_B(g)^{\otimes n}}\circ M\quad(g\in G)$$
--   satisfies F1–F5 with those witnesses. Any indexed intersection of families satisfying F1–F5 with the same faithful witnesses also satisfies all five conditions; the empty intersection is the set of all CPTP maps. This requires no finite-group or topological assumption on $G$.
-- source:
--   A Generalized Stein Lemma for Quantum Channels, arXiv:2609.30762v1, PDF p. 22, Proposition 21

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Information100.P69

attribute [local instance] Classical.propDecidable Classical.decEq

section Statements

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Proposition 21, arbitrary groups and arbitrary intersections with common witnesses, PDF p.22. -/
theorem covarianceAndIntersections [Nonempty A] [Nonempty B] :
    (∀ (G : Type*) [Group G] (UA : G → Matrix A A ℂ) (UB : G → Matrix B B ℂ),
      (∀ g, (UA g).conjTranspose*UA g = 1) → (∀ g, (UB g).conjTranspose*UB g = 1) →
      UA 1 = 1 → UB 1 = 1 → (∀ g h, UA (g*h) = UA g*UA h) → (∀ g h, UB (g*h) = UB g*UB h) →
      ∀ tau : Matrix A A ℂ, ∀ omega : Matrix B B ℂ, Faithful tau → Faithful omega →
      (∀ g, conjSuperop (UA g) tau = tau) → (∀ g, conjSuperop (UB g) omega = omega) →
        Admissible (covariantFamily UA UB) omega ∧ Additional (covariantFamily UA UB) tau) ∧
    (∀ (I : Type*) (F : I → BlockFamily A B) (tau : Matrix A A ℂ) (omega : Matrix B B ℂ),
      Faithful tau → Faithful omega → (∀ i, Admissible (F i) omega ∧ Additional (F i) tau) →
        Admissible (fun n => {M | IsChannel M ∧ ∀ i, M ∈ F i n}) omega ∧
        Additional (fun n => {M | IsChannel M ∧ ∀ i, M ∈ F i n}) tau) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Information100.P69

end
