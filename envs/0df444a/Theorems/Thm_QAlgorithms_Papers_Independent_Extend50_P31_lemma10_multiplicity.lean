-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_lemma10_multiplicity
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.lemma10_multiplicity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:30:11.499286+00:00
-- url     : https://prove2.me/theorems/2a4c7d8c-7507-471f-9013-5f74ec5b5bf9
-- title:
--   Lemma 10: trivial multiplicity and commutant dimension
-- statement:
--   Let $G$ be finite, let $U:G\to U(n)$ be unitary irreducible, $n>0$, and fix a complete family $\{\varphi^\alpha\}$ of inequivalent unitary irreducibles, with trivial label $\mathrm{id}$. There exist nonnegative integer multiplicities $m_\alpha$ giving an intertwining decomposition, and
--
--   $$
--   U\otimes\overline U\simeq\bigoplus_\alpha m_\alpha\varphi^\alpha,\qquad m_{\mathrm{id}}=1,\qquad \dim_{\mathbb C}\operatorname{Int}_G(U\otimes\overline U)=\frac1{|G|}\sum_{g\in G}|\chi_U(g)|^4.
--   $$
--
--   The one-dimensional case is included. This computes the trivial multiplicity and the commutant dimension without imposing multiplicity-freeness.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 9, Lemma 10: trivial multiplicity and commutant dimension

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Extend50.P31

open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Bridge50.P37 (hsAdjoint)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)

open QAlgorithms.Papers.Independent.Information100.P75 (phase)

variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}

/-- PDF p.9, Lemma 10 Eqs.(37),(38). Includes n=1; the fourth power is of the modulus. -/
theorem lemma10_multiplicity (U : UnitaryIrrep G n) (F : IrrepFamily G A) :
    (∃ m : A → ℕ, HasDecomposition U F m ∧ m F.trivial = 1) ∧
    (Module.finrank ℂ (representationCommutant (tensorConjugate U)) : ℝ) =
      (Fintype.card G : ℝ)⁻¹ * ∑ g : G, ‖character U g‖^4 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
