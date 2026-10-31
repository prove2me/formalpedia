-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P63_regularization_exists
-- name    : QAlgorithms.Papers.Independent.Intake100.P63.regularization_exists
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:13:28.365578+00:00
-- url     : https://prove2.me/theorems/99ca3088-27f8-4ca6-85f8-39d8065f11a9
-- title:
--   §II, unnumbered: existence of the regularized relative-entropy limit
-- statement:
--   Let $H$ be a nonzero finite-dimensional complex Hilbert space and let $\rho\in\mathcal D(H)$ be a normalized density operator. For each positive integer $n$, let $M_n\subseteq\mathcal D(H^{\otimes n})$ be closed and convex. Assume that one fixed full-rank state $\sigma$ has $\sigma^{\otimes n}\in M_n$ for every positive $n$, that every single-copy partial trace preserves the family, that tensor products map $M_n\times M_m$ into $M_{n+m}$, and that conjugation by every copy permutation preserves $M_n$. Define $E_{M_n}(\xi)=\inf_{\omega\in M_n}D_2(\xi\Vert\omega)$, using base-two relative entropy with value $+\infty$ on failed support inclusion, and define $E_M^\infty(\rho)=\inf_{n\ge1}E_{M_n}(\rho^{\otimes n})/n$.
--
--   Every positive-block quantity and the regularized value are finite, and
--   $$
--   \lim_{n\to\infty}\frac{E_{M_n}(\rho^{\otimes n})}{n}
--   =\inf_{n\ge1}\frac{E_{M_n}(\rho^{\otimes n})}{n}=E_M^\infty(\rho)<+\infty.
--   $$
--
--   This identifies the regularized entropy from its finite-copy construction; convergence and finiteness are conclusions.
-- source:
--   A Generalization of Quantum Stein's Lemma, arXiv:0904.0281v3, PDF p. 5, §II, unnumbered: existence of the regularized relative-entropy limit

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

/-- PDF p.5 Eq.(10), unnumbered regularization claim: finiteness and convergence
are conclusions, not hypotheses; the positive-block infimum equals the limit. -/
theorem regularization_exists {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (M : (n : ℕ) → Set (Mat (Copies I n))) (hM : stateSetAxioms M)
    (rho : Mat I) (hrho : IsDensityMatrix rho) :
    regularizedSetEntropy M rho ≠ ⊤ ∧
    (∀ n, 0 < n → setEntropy (M n) (piKron n rho) ≠ ⊤) ∧
    Tendsto (fun n => setEntropy (M n) (piKron n rho) / (n : ℝ≥0∞))
      atTop (𝓝 (regularizedSetEntropy M rho)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P63

end
