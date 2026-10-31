-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P63_diagonal_smoothing
-- name    : QAlgorithms.Papers.Independent.Intake100.P63.diagonal_smoothing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:18:57.537248+00:00
-- url     : https://prove2.me/theorems/ca74e6e0-811a-49e9-9693-647e80fb4fea
-- title:
--   Corollary III.2: diagonal smoothing formula
-- statement:
--   Let $H$ be a nonzero finite-dimensional complex Hilbert space and let $\rho\in\mathcal D(H)$ be a normalized density operator. For each positive integer $n$, let $M_n\subseteq\mathcal D(H^{\otimes n})$ be closed and convex. Assume that one fixed full-rank state $\sigma$ has $\sigma^{\otimes n}\in M_n$ for every positive $n$, that every single-copy partial trace preserves the family, that tensor products map $M_n\times M_m$ into $M_{n+m}$, and that conjugation by every copy permutation preserves $M_n$. Define $E_{M_n}(\xi)=\inf_{\omega\in M_n}D_2(\xi\Vert\omega)$, using base-two relative entropy with value $+\infty$ on failed support inclusion, and define $E_M^\infty(\rho)=\inf_{n\ge1}E_{M_n}(\rho^{\otimes n})/n$.
--
--   Use $LR_{M_n}^\epsilon$ for the max-relative entropy to $M_n$, smoothed over normalized states in the closed full trace-norm $\epsilon$-ball. Choose the entire sequence of radii before taking the asymptotic envelope:
--   $$
--   LG_M(\rho):=\inf_{\substack{\epsilon_n\ge0\\\epsilon_n\to0}}\limsup_{n\to\infty}\frac{LR_{M_n}^{\epsilon_n}(\rho^{\otimes n})}{n}
--   =E_M^\infty(\rho).
--   $$
--
--   Zero radii are allowed; neither monotonicity nor a prescribed decay rate is required.
-- source:
--   A Generalization of Quantum Stein's Lemma, arXiv:0904.0281v3, PDF p. 10, Corollary III.2: diagonal smoothing formula

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P63

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P63

open QAlgorithms Filter Topology

open QAlgorithms.Papers.Independent.Information100.P60 (Mat relativeBits)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart)

open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Advance50.P30 (joinCopies defectTensor)

open QAlgorithms.Papers.Independent.Information100.P69 (permute)

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.10 Corollary III.2 Eq.(46), with the entire smoothing sequence
optimized as in Eq.(45). -/
theorem diagonal_smoothing {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (M : (n : ℕ) → Set (Mat (Copies I n))) (hM : stateSetAxioms M)
    (rho : Mat I) (hrho : IsDensityMatrix rho) :
    diagonalSmooth M rho = regularizedSetEntropy M rho := by sorry

end QAlgorithms.Papers.Independent.Intake100.P63

end
