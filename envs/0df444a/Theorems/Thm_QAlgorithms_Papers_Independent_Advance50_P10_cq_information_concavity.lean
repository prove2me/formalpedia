-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P10_cq_information_concavity
-- name    : QAlgorithms.Papers.Independent.Advance50.P10.cq_information_concavity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:57:30.361199+00:00
-- url     : https://prove2.me/theorems/8bc87cb9-f9eb-4b73-bbe0-22ee0c245bc3
-- title:
--   Lemma B.1: concavity of cq Renyi information
-- statement:
--   All logarithms are base two. On a finite-dimensional complex Hilbert space $H$, write $S_\alpha(A\|B)$ for the paper’s unnormalized Petz Rényi relative entropy of positive semidefinite operators, with extended-real values, support-only powers, and the Umegaki value at order one. Let $X$ be an arbitrary nonempty alphabet and $W:X\to\mathcal S(H)$ a classical–quantum channel with density outputs. Input laws are nonnegative finitely supported probability laws. For such a law $p$, let $\widehat W_p=\sum_xp(x)|x\rangle\langle x|\otimes W_x$ and $\widehat p=\sum_xp(x)|x\rangle\langle x|$. Define $\chi_\alpha(p)=\inf_{\sigma\in\mathcal S(H)}S_\alpha(\widehat W_p\|\widehat p\otimes\sigma)$ and $\chi^*_{\alpha,1}(W)=\sup_p\chi_\alpha(p)$. Fix $\alpha>1$. For any finite laws $p,q$, any $0<t<1$, their mixture $r=(1-t)p+tq$, and any density centre $\sigma$,
--
--   $$S_\alpha(\widehat W_r\|\widehat r\otimes\sigma)\ge(1-t)S_\alpha(\widehat W_p\|\widehat p\otimes\sigma)+tS_\alpha(\widehat W_q\|\widehat q\otimes\sigma)\ge(1-t)\chi_\alpha(p)+t\chi_\alpha(q).$$
--
--   Moreover $\chi_\alpha(r)\ge(1-t)\chi_\alpha(p)+t\chi_\alpha(q)$. Different supports are allowed and can be embedded into their finite union. This establishes concavity in the input law for type-1 information.
-- source:
--   On the quantum Renyi relative entropies and related capacity formulas, arXiv:0912.1286v4, PDF p. 11, Lemma B.1: concavity of cq Renyi information

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

/-- Lemma B.1, PDF p.11: the full fixed-centre chain and concavity after
minimizing the centre. Distinct supports are handled by each law's own finite lift. -/
theorem cq_information_concavity {X I : Type} [Nonempty X] [Fintype I] [DecidableEq I]
    (W : X → Operator I) (hW : ∀ x, IsDensityMatrix (W x)) (a : ℝ) (ha : 1 < a) :
    ∀ p q r : FinitelySupportedInputLaw X, ∀ t : ℝ, 0 < t → t < 1 →
      r.1 = (1 - t) • p.1 + t • q.1 →
      (∀ sigma : {A : Operator I // IsDensityMatrix A},
        ((1 - t : ℝ) : EReal) * lawObjective a W p sigma.1 +
          (t : EReal) * lawObjective a W q sigma.1 ≤ lawObjective a W r sigma.1 ∧
        ((1 - t : ℝ) : EReal) * petzLawInformationBits a W p +
          (t : EReal) * petzLawInformationBits a W q ≤
        ((1 - t : ℝ) : EReal) * lawObjective a W p sigma.1 +
          (t : EReal) * lawObjective a W q sigma.1) ∧
      ((1 - t : ℝ) : EReal) * petzLawInformationBits a W p +
        (t : EReal) * petzLawInformationBits a W q ≤ petzLawInformationBits a W r := by sorry

end QAlgorithms.Papers.Independent.Advance50.P10

end
