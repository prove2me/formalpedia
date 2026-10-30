-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_s4_spectrum
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.s4_spectrum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:00:53.64824+00:00
-- url     : https://prove2.me/theorems/6382c0c2-1d49-403b-8fb4-458f893283b3
-- title:
--   Section 8.4, Eq.(149): Choi spectrum of the S(4) triplet spectral family
-- statement:
--   For the $S_4$ triplet of partition $(3,1)$ construct $\Phi=P_{\mathrm{id}}+aP_{(3,1)}+bP_{(2,2)}+cP_{(2,1,1)}$ by character averages, with $a,b,c\in\mathbb R$. Its Choi matrix has a complete orthonormal eigenbasis with spectrum
--
--   $$
--   \left\{\frac{1+3a+2b+3c}{3}\ [1],\quad\frac{2+3a-2b-3c}{6}\ [3],\quad\frac{2-3a+4b-3c}{6}\ [2],\quad\frac{2-3a-2b+3c}{6}\ [3]\right\}.
--   $$
--
--   Brackets give multiplicities $1,3,2,3$. The map is CPTP exactly when all four displayed values are nonnegative. The third line of the source has a repeated label; it belongs to $(2,1,1)$. This spectrum concerns the character-projector family, independently of disputed entrywise formulas.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 29, Section 8.4, Eq.(149): Choi spectrum of the S(4) triplet spectral family

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

/-- PDF p.29 Eq.(149): spectrum with all nine multiplicities of the character-projector family.
SOURCE CORRECTION: first superscript in Eq.(149)'s third line is lambda3, not lambda1;
its other two entries and the three-dimensional sector determine the label. -/
theorem s4_spectrum (U : UnitaryIrrep (Equiv.Perm (Fin 4)) 3)
    (hU : ∀ g, character U g = s4StandardCharacter g) (a b c : ℝ) :
    HasOrthonormalSpectrum (choi (s4Map U a b c)) (s4Eigenvalues a b c) ∧
    (IsPaperChannel (s4Map U a b c) ↔ ∀ i : Fin 9, 0 ≤ s4Eigenvalues a b c i) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
