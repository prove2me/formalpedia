-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P36_optimalInput
-- name    : QAlgorithms.Papers.Independent.Next46.P36.optimalInput
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:38:02.714014+00:00
-- url     : https://prove2.me/theorems/4ea8f460-99a3-417d-af7b-46fd41816515
-- title:
--   Theorem 1: optimal canonical input states
-- statement:
--   Let $G$ be a compact group with normalized two-sided Haar measure, and let $U_g^\mu$ be the occurring pairwise inequivalent, positive-dimensional continuous unitary irreducible representations. Work on $H_{\rm can}=\bigoplus_{\mu\in S}H_\mu\otimes\mathbb C^{d_\mu}$, where $S$ is finite and nonempty. Let $c(\hat g,g)$ be a real, integrable, left- and right-invariant generalized Holevo cost: its real character coefficients $a_\sigma$ are nonpositive for nontrivial $\sigma$, and equal on dual irreducibles; $a_0$ is unrestricted.
--
--   There exist nonnegative magnitudes $v_\mu$, chosen before any block unitaries, such that $\sum_\mu v_\mu^2=1$ and, for every collection of unitary matrices $W_\mu$, the normalized input
--
--   $$\Psi=\bigoplus_\mu\frac{v_\mu}{\sqrt{d_\mu}}\operatorname{vec}(W_\mu)$$
--
--   admits a normalized covariant measurement achieving the global minimum Haar-average cost over all admissible density-matrix inputs and all measurements on the canonical space. One may use the rank-one seed with vector $\eta=\bigoplus_\mu\sqrt{d_\mu}\operatorname{vec}(W_\mu)$.
--
--   This identifies an optimal input form without asserting that every optimal input has that form.
-- source:
--   Optimal estimation of group transformations using entanglement, arXiv:quant-ph/0506267v2, PDF p. 4, Theorem 1

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P36

noncomputable section

open MeasureTheory Filter

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Next46.P36

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P36.matrixMeasurable

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- PDF p.4 Theorem 1, with the sharp universal seed from p.6 Theorem 2.
The optimal nonnegative magnitudes are chosen before the block unitaries. -/
theorem optimalInput
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (D : S → BasedIrrep G) (hD : OccurringIrrepsInequivalent D)
    (dg : Measure G) [IsProbabilityMeasure dg]
    [Measure.IsMulLeftInvariant dg] [Measure.IsMulRightInvariant dg]
    (K : IrrepCatalog G) (cost : G → G → ℝ) (hc : HolevoCost dg K cost) :
    ∃ v : S → ℝ, (∀ s, 0 ≤ v s) ∧ (∑ s, (v s) ^ 2) = 1 ∧
      ∀ W : ∀ s, Matrix.unitaryGroup (Fin (D s).dim) ℂ,
      ∃ M : QAlgorithms.Measurements.DensityPOVM (CanonicalIndex D) G,
        QAlgorithms.IsState (canonicalInput D (fun s => (v s : ℂ)) W) ∧
        M.reference = dg ∧
        (∀ g, M.density g = QAlgorithms.conjSuperop (canonicalAction D g)
          (QAlgorithms.pureDensity (likelihoodVector D (fun s => (v s : ℂ)) W))) ∧
        GlobalOptimal D dg cost (QAlgorithms.pureDensity (canonicalInput D (fun s => (v s : ℂ)) W)) M := by sorry

end QAlgorithms.Papers.Independent.Next46.P36

end
