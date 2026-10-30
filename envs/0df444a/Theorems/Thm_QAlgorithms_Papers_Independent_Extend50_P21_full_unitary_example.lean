-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P21_full_unitary_example
-- name    : QAlgorithms.Papers.Independent.Extend50.P21.full_unitary_example
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:15:51.536919+00:00
-- url     : https://prove2.me/theorems/7c376324-7317-4392-b243-fc09e2afa494
-- title:
--   Example 20: full-unitary covariance and a two-dimensional program
-- statement:
--   All Hilbert spaces are nonzero and finite dimensional over $\mathbb C$. Channels are completely positive and trace preserving (CPTP), density operators are positive semidefinite with trace one, and pure programs are unit vectors. The normalized, reference-first Choi operator is $c_T=(\mathrm{id}_{d_1}\otimes T)(|\Omega\rangle\langle\Omega|)$, where $|\Omega\rangle=d_1^{-1/2}\sum_i|i,i\rangle$, with two input-sized factors before $T$ acts. Let $d\ge2$ and let $U$ be the defining representation of $U(d)$. The tensor representation $\overline U\otimes U$ has the trivial irreducible and an irreducible of dimension $d^2-1$, each once. Its covariant CPTP maps are exactly
--
--   $$T_\alpha(A)=\alpha\operatorname{tr}(A)I_d/d+(1-\alpha)A,\qquad 0\le\alpha\le\frac{d^2}{d^2-1}.$$
--
--   Their Choi operators are $\alpha I_{d^2}/d^2+(1-\alpha)|\Omega\rangle\langle\Omega|$, the segment with endpoints $|\Omega\rangle\langle\Omega|$ and $(I-|\Omega\rangle\langle\Omega|)/(d^2-1)$. One fixed exact measure-and-prepare processor for the whole class has program dimension two and pure programs. The channel characterization is attributed to [26,40]; the processor is the paper application.
-- source:
--   Programmability of covariant quantum channels, arXiv:2012.00717v2, PDF p. 10, Example 20: full-unitary covariance and a two-dimensional program

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Manifold ContDiff

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

open QAlgorithms.Papers.Independent.Support21.P09 (Irreducible EquivalentModels)

open QAlgorithms.Papers.Independent.Information100.P69 (diamond)

open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

namespace QAlgorithms.Papers.Independent.Extend50.P21

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF pp.10--11, Example 20: the full depolarizing segment and a two-dimensional
measure-and-prepare program. d>=2 excludes the vanishing second summand. -/
theorem full_unitary_example (d : ℕ) (hd : 2 ≤ d) :
    (∃ U : ContinuousUnitaryRep (Matrix.unitaryGroup (Fin d) ℂ) (Fin d),
      (∀ W : Matrix.unitaryGroup (Fin d) ℂ, U.mat W = (W : Matrix (Fin d) (Fin d) ℂ)) ∧ Irreducible U.mat ∧
      ∃ D : TensorIsotypicDecomposition U U, D.count = 2 ∧ ∃ k : Fin D.count,
        D.degree k = 1 ∧ (∀ g, (D.component k).mat g = 1) ∧
        (∀ l, D.copies l = 1) ∧ (∀ l, l ≠ k → D.degree l = d ^ 2 - 1)) ∧
    (∀ T : Superop (Fin d) (Fin d), T ∈ fullUnitaryClass d ↔
      ∃ alpha : ℝ, 0 ≤ alpha ∧ alpha ≤ (d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1) ∧
        T = depolarizing d alpha) ∧
    (∀ alpha : ℝ, 0 ≤ alpha → alpha ≤ (d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1) →
      normalizedChoi (depolarizing d alpha) =
      (alpha / (d : ℝ) ^ 2 : ℝ) • (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) +
        (1 - alpha) • omegaDensity d) ∧
    (choiSet (fullUnitaryClass d) = convexHull ℝ
      {omegaDensity d, (((d : ℝ) ^ 2 - 1)⁻¹) • (1 - omegaDensity d)}) ∧
    (∃ processor : Superop (Fin d × Fin 2) (Fin d),
      PureImplements processor (fullUnitaryClass d) 0 ∧
      FiniteMeasurePrepareProcessor processor (fullUnitaryClass d)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P21

end
