-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P36_maximumLikelihoodSeed
-- name    : QAlgorithms.Papers.Independent.Next46.P36.maximumLikelihoodSeed
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T14:42:41.702009+00:00
-- url     : https://prove2.me/theorems/558a520b-cf8d-45a1-a717-8094a60374ca
-- title:
--   Remark II: maximum likelihood among continuous covariant densities
-- statement:
--   Let a compact group act through a finite nonempty canonical unitary representation with positive-dimensional inequivalent irreducible blocks. Use normalized Haar measure and fix a canonical input with normalized coefficients $c_\mu$ and block unitaries $W_\mu$. The seed $\Xi_{\rm ML}=|\eta\rangle\langle\eta|$, where $\eta$ is the vector of Theorem 2 with phase one at zero coefficients, is normalized as a covariant POVM and satisfies
--
--   $$p_\Xi(g\mid g)\le p_{\Xi_{\rm ML}}(g\mid g)\quad\text{for every normalized covariant seed }\Xi\text{ and every }g\in G.$$
--
--   Each likelihood is evaluated on its continuous covariant density $U_g\Xi U_g^\dagger$ and the actual orbit state. This identifies the same universal seed without treating a Dirac delta as an ordinary cost function or optimizing arbitrary pointwise versions of densities.
-- source:
--   Optimal estimation of group transformations using entanglement, arXiv:quant-ph/0506267v2, PDF p. 7, §III F Remark II

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P36

noncomputable section

open MeasureTheory Filter

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Next46.P36

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P36.matrixMeasurable

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- PDF p.7 Remark II: maximize the continuous covariant likelihood density.
This does not interpret a Dirac distribution as an ordinary real cost function. -/
theorem maximumLikelihoodSeed
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (D : S → BasedIrrep G) (hD : OccurringIrrepsInequivalent D)
    (dg : Measure G) [IsProbabilityMeasure dg]
    [Measure.IsMulLeftInvariant dg] [Measure.IsMulRightInvariant dg]
    (c : S → ℂ) (hn : (∑ s, Complex.normSq (c s)) = 1)
    (W : ∀ s, Matrix.unitaryGroup (Fin (D s).dim) ℂ) :
    NormalizedSeed D dg (QAlgorithms.pureDensity (likelihoodVector D c W)) ∧
    ∀ Xi, NormalizedSeed D dg Xi → ∀ g,
      QAlgorithms.effectProb (QAlgorithms.conjSuperop (canonicalAction D g) Xi)
        (QAlgorithms.conjSuperop (canonicalAction D g) (QAlgorithms.pureDensity (canonicalInput D c W))) ≤
      QAlgorithms.effectProb
        (QAlgorithms.conjSuperop (canonicalAction D g) (QAlgorithms.pureDensity (likelihoodVector D c W)))
        (QAlgorithms.conjSuperop (canonicalAction D g) (QAlgorithms.pureDensity (canonicalInput D c W))) := by sorry

end QAlgorithms.Papers.Independent.Next46.P36

end
