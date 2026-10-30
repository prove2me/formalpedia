-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P29_reference_frame_covariant_equivalence
-- name    : QAlgorithms.Papers.Independent.Extend50.P29.reference_frame_covariant_equivalence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:10:17.290993+00:00
-- url     : https://prove2.me/theorems/32b81d78-9ec7-47d4-9a9e-744720ae8c4a
-- title:
--   Reference frame error correction / Covariant error correction: equivalence via Haar twirling
-- statement:
--   Let $G$ be a compact Hausdorff topological group with normalized probability Haar measure, acting continuously and unitarily on a nonzero finite-dimensional input and $n\ge1$ nonzero finite-dimensional output registers. Fix CPTP decoders $\mathcal D_j$ for the known erased sites. Write
--   $$\mathcal E_g(\rho)=U_{\rm out}(g)\mathcal E(U_{\rm in}(g)^\dagger\rho U_{\rm in}(g))U_{\rm out}(g)^\dagger,$$
--   where $U_{\rm out}=\bigotimes_i U_i$. Then
--   $$\exists\mathcal E_A\ \forall g,j,\rho:\ \mathcal D_j\operatorname{Tr}_j\mathcal E_{A,g}(\rho)=\rho
--   \quad\Longleftrightarrow\quad
--   \exists\mathcal E\text{ covariant}\ \forall j,\rho:\ \mathcal D_j\operatorname{Tr}_j\mathcal E(\rho)=\rho.$$
--   All encoders here are CPTP, and $\rho$ ranges over every input density matrix. The forward construction is the integrable Haar average $\mathcal E=\int_G\mathcal E_{A,g}\,dg$, with the same decoders. The reverse construction uses $\mathcal E_A=\mathcal E$. This includes the source's $SO(3)$ reference-frame task.
-- source:
--   Error Correction of Quantum Reference Frame Information, arXiv:1709.04471v1, PDF p. 3, Reference frame error correction / Covariant error correction: equivalence via Haar twirling

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P29

noncomputable section

open MeasureTheory MeasureTheory.Measure

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Extend50.P29

open QAlgorithms.Papers.Independent.Information100.P32 (evolution)

open QAlgorithms.Papers.Independent.Next46.P39 (inverseSqrt rectAct)

open QAlgorithms.Papers.Independent.Support21.P09 (groupLeftRegular)

/-- PDF pp.2--3: reference-frame and covariant correction are equivalent.
The constructive clauses retain the given decoder family and use the actual Haar
average in the forward direction. Compact Hausdorff G includes SO(3). -/
theorem reference_frame_covariant_equivalence
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsHaarMeasure μ] [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 1 ≤ n) {I : Type} [Fintype I] [Nonempty I]
    {H : Fin n → Type} [∀ i, Fintype (H i)] [∀ i, Nonempty (H i)]
    (Ui : G →* Matrix.unitaryGroup I ℂ)
    (Uo : (i : Fin n) → G →* Matrix.unitaryGroup (H i) ℂ)
    (hcUi : Continuous Ui) (hcUo : ∀ i, Continuous (Uo i))
    (D : Decoders (I := I) H) (hD : ∀ j, IsChannel (D j)) :
    let ui := fun g => (Ui g : Matrix I I ℂ)
    let uo := fun g i => (Uo i g : Matrix (H i) (H i) ℂ)
    ((∃ E, IsChannel E ∧ ReferenceSuccess ui uo E D) ↔
      (∃ E, IsChannel E ∧ ErasureCovariant ui uo E ∧ SingleCorrects E D)) ∧
    (∀ E, IsChannel E → ReferenceSuccess ui uo E D →
      (∀ X, Integrable (fun g => rotatedEncoding ui uo E g X) μ) ∧
      IsChannel (twirledEncoding μ ui uo E) ∧
      ErasureCovariant ui uo (twirledEncoding μ ui uo E) ∧
      SingleCorrects (twirledEncoding μ ui uo E) D) ∧
    (∀ E, IsChannel E → ErasureCovariant ui uo E → SingleCorrects E D →
      ReferenceSuccess ui uo E D) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P29

end
