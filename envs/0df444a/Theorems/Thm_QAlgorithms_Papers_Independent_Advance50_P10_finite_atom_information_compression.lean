-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P10_finite_atom_information_compression
-- name    : QAlgorithms.Papers.Independent.Advance50.P10.finite_atom_information_compression
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:58:56.333652+00:00
-- url     : https://prove2.me/theorems/245645ce-e39a-44d2-a340-03caf95f4046
-- title:
--   Unnumbered: finite-atom compression of fixed-law information
-- statement:
--   All logarithms are base two. On a finite-dimensional complex Hilbert space $H$, write $S_\alpha(A\|B)$ for the paper’s unnormalized Petz Rényi relative entropy of positive semidefinite operators, with extended-real values, support-only powers, and the Umegaki value at order one. Let $X$ be an arbitrary nonempty alphabet and $W:X\to\mathcal S(H)$ a classical–quantum channel with density outputs. Input laws are nonnegative finitely supported probability laws. For such a law $p$, let $\widehat W_p=\sum_xp(x)|x\rangle\langle x|\otimes W_x$ and $\widehat p=\sum_xp(x)|x\rangle\langle x|$. Define $\chi_\alpha(p)=\inf_{\sigma\in\mathcal S(H)}S_\alpha(\widehat W_p\|\widehat p\otimes\sigma)$ and $\chi^*_{\alpha,1}(W)=\sup_p\chi_\alpha(p)$. Let $d=\dim H$, $m=d^2+1$ and $\alpha\ge0$. Write $\widetilde\chi_\alpha$ for the same infimum-defined information when the alphabet is $\operatorname{ran}W$ and the channel is inclusion. Every finite law $p$ on $X$ admits a finite law $\widetilde p$ on $\operatorname{ran}W$ such that
--
--   $$|\operatorname{supp}\widetilde p|\le d^2+1,\qquad\chi_\alpha(p)=\widetilde\chi_\alpha(\widetilde p).$$
--
--   Consequently $\chi^*_{\alpha,1}(W)=\sup_{|\operatorname{supp}\widetilde p|\le d^2+1}\widetilde\chi_\alpha(\widetilde p)$. No compactness hypothesis is imposed here. At zero and one the quantities retain their infimum definitions rather than an invalid power formula. This compresses the optimization to a fixed number of atoms.
-- source:
--   On the quantum Renyi relative entropies and related capacity formulas, arXiv:0912.1286v4, PDF p. 11, Unnumbered: finite-atom compression of fixed-law information

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P10

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate ENNReal Topology

open Filter Set MeasureTheory

namespace QAlgorithms.Papers.Independent.Advance50.P10

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P58 (Operator)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart)

open QAlgorithms.Papers.Independent.Dependency50.P18 (logBits)

open QAlgorithms.Papers.Independent.Dependency50.P25 (extendedIntegral)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Bridge50.P45 (tensorEntries lifted comparison)

-- Density subtypes below reuse the frozen PSD/trace-one predicate directly.

-- The source uses Borel laws, with the weak topology on probability measures.

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P10.densityMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P10.densityBorelSpace

/-- Finite-atom compression and its optimization consequence, PDF pp.11–12.
The universal bound is d^2+1, exactly the source's bound. At zero and one the
information is defined through the infimum, never through an invalid 1/a formula. -/
theorem finite_atom_information_compression {X I : Type} [Nonempty X] [Fintype I] [DecidableEq I]
    (W : X → Operator I) (hW : ∀ x, IsDensityMatrix (W x)) (a : ℝ) (ha : 0 ≤ a) :
    (∀ p : FinitelySupportedInputLaw X, ∃ q : FinitelySupportedInputLaw (Set.range W),
      q.1.support.card ≤ Fintype.card I ^ 2 + 1 ∧
      petzLawInformationBits a W p = petzLawInformationBits a (fun rho : Set.range W => rho.1) q) ∧
    capacityOne a W =
      ⨆ q : {q : FinitelySupportedInputLaw (Set.range W) // q.1.support.card ≤ Fintype.card I ^ 2 + 1},
        petzLawInformationBits a (fun rho : Set.range W => rho.1) q.1 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P10

end
