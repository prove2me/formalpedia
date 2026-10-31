-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P70_lemma1_2_orthogonal_images
-- name    : QAlgorithms.Papers.Independent.Intake100.P70.lemma1_2_orthogonal_images
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:40:05.186326+00:00
-- url     : https://prove2.me/theorems/3ebe1764-6818-491e-ae4a-6727208c0aff
-- title:
--   Lemma 1.2: positive and negative images have disjoint supports
-- statement:
--   Let $\mathcal E$ be a CPTP map between finite-dimensional nonzero complex Hilbert spaces, and let $C$ be a convex set of positive matrices of ordinary trace one. Preservation means equality of $\|\mathcal E(p\rho-(1-p)\sigma)\|_1$ and $\|p\rho-(1-p)\sigma\|_1$ for every $\rho,\sigma\in C$ and $p\in[0,1]$. For a preserved $C$, choose $\rho,\sigma\in C$, $p\in[0,1]$, and form the spectral positive and negative parts $\Delta_\pm$ of $\Delta=p\rho-(1-p)\sigma$. Then
--
--   $$\operatorname{supp}\mathcal E(\Delta_+)\;\operatorname{supp}\mathcal E(\Delta_-)=0.$$
--
--   Orthogonality of the two image supports captures the preserved Helstrom separation. The proof uses trace preservation.
-- source:
--   Information preserving structures: A general framework for quantum zero-error information, arXiv:1006.1358v1, PDF p. 21, Lemma 1.2: positive and negative images have disjoint supports

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P70

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intake100.P70

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

/-- PDF p.21, Lemma 1.2. TP is retained because Eq.(B1) uses it.
Positive and negative parts are computed, and disjoint means orthogonal supports. -/
theorem lemma1_2_orthogonal_images {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (E : Superop I J) (hE : IsChannel E) (C : Set (Op I)) (hC : IsCode C)
    (hPres : Preserved E C) (rho sigma : Op I) (hr : rho ∈ C) (hs : sigma ∈ C)
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    supportProjector (E (positivePart (weighted p rho sigma))) *
      supportProjector (E (negativePart (weighted p rho sigma))) = 0 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P70

end
