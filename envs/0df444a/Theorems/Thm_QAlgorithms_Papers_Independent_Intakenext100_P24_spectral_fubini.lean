-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P24_spectral_fubini
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P24.spectral_fubini
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T22:57:08.18465+00:00
-- url     : https://prove2.me/theorems/0242040f-84d7-405c-a3a8-0b1150ad673e
-- title:
--   Fubini identity for commuting spectral measures with bounded right factor
-- statement:
--   Let $\Omega_1,\Omega_2$ be locally compact Hausdorff spaces with countable open bases. Let $E_1,E_2$ be normalized orthogonal projection-valued Borel measures on these spaces, countably additive in the strong operator topology and acting on the same arbitrary complex Hilbert space $H$. Assume that
--
--   $$
--   E_1(A)E_2(B)=E_2(B)E_1(A)
--   $$
--
--   for every pair of Borel sets $A\subseteq\Omega_1$ and $B\subseteq\Omega_2$. Let $f_1:\Omega_1\to\mathbb C$ and $f_2:\Omega_2\to\mathbb C$ be finite-valued Borel functions, with $f_2$ bounded on all of $\Omega_2$.
--
--   The product spectral measure $P=E_1\times E_2$ is the unique normalized Borel PVM satisfying $P(A\times B)=E_1(A)E_2(B)$ on Borel rectangles, as supplied by Theorem 3.1. Then
--
--   $$
--   \left(\int_{\Omega_1}f_1\,dE_1\right)
--   \left(\int_{\Omega_2}f_2\,dE_2\right)
--   =
--   \int_{\Omega_1\times\Omega_2}f_1(\omega_1)f_2(\omega_2)\,P(d\omega_1\,d\omega_2).
--   $$
--
--   The right operator is applied first in the product on the left. Both sides have the same actual domain; no closure is taken. The first function may be unbounded. This identity is the spectral product rule used to derive the unbounded representation theorem from bounded spectral measures.
--
--   **Formalization Note.** Existence and uniqueness from the inherited product-measure specification, and validity of the selected product measure, are included in the conclusion. They justify the choice without adding an existence hypothesis. The product sigma algebra is the Borel sigma algebra of the product under these countability assumptions.
-- source:
--   Decomposition of Normal Operators and Its Application to Spectral Theorem, arXiv:2006.04644v2, PDF p. 3, Theorem 3.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P24

noncomputable section

attribute [local instance] Classical.propDecidable

open Set MeasureTheory

open scoped Topology

open QAlgorithms.Papers.Independent.Claimed50.P05

namespace QAlgorithms.Papers.Independent.Intakenext100.P24

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Theorem 3.2, PDF pp.3–4, using the product defined after Theorem 3.1.
The product-existence and uniqueness statement recalled in Theorem 3.1 is
included as a conclusion to justify the choice and its PVM guard; it is not
an extra hypothesis. Both base spaces have exactly the source's locally
compact, Hausdorff, countable-base assumptions, and the measurable product
is their Borel product. The right symbol is bounded; the left may be
unbounded. No closure is taken in the graph equality (Remark 3.3, p.4). -/
theorem spectral_fubini
    {Omega1 Omega2 : Type*}
    [TopologicalSpace Omega1] [TopologicalSpace Omega2]
    [LocallyCompactSpace Omega1] [LocallyCompactSpace Omega2]
    [T2Space Omega1] [T2Space Omega2]
    [SecondCountableTopology Omega1] [SecondCountableTopology Omega2]
    [MeasurableSpace Omega1] [MeasurableSpace Omega2]
    [BorelSpace Omega1] [BorelSpace Omega2]
    (E1 : {A : Set Omega1 // MeasurableSet A} → Relation H)
    (E2 : {B : Set Omega2 // MeasurableSet B} → Relation H)
    (hE1 : PVM (k := ℂ) E1) (hE2 : PVM (k := ℂ) E2)
    (hcomm : ∀ (A : Set Omega1) (B : Set Omega2)
      (hA : MeasurableSet A) (hB : MeasurableSet B),
      mul (E1 ⟨A, hA⟩) (E2 ⟨B, hB⟩) = mul (E2 ⟨B, hB⟩) (E1 ⟨A, hA⟩))
    (f1 : QAlgorithms.Papers.Independent.Claimed50.P05.Symbol Omega1 ℂ) (f2 : QAlgorithms.Papers.Independent.Claimed50.P05.Symbol Omega2 ℂ) (hf2 : BoundedSymbol f2) :
    (∃! P, IsProductSpectralMeasure E1 E2 P) ∧
    IsProductSpectralMeasure E1 E2 (productSpectralMeasure E1 E2) ∧
    mul (pvmOperatorIntegral E1 f1) (pvmOperatorIntegral E2 f2) =
      pvmOperatorIntegral (productSpectralMeasure E1 E2)
        ⟨fun p => f1.val p.1 * f2.val p.2,
          (f1.property.comp measurable_fst).mul (f2.property.comp measurable_snd)⟩ := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P24

end
