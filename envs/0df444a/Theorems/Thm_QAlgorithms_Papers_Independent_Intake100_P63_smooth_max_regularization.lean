-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P63_smooth_max_regularization
-- name    : QAlgorithms.Papers.Independent.Intake100.P63.smooth_max_regularization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:15:31.705991+00:00
-- url     : https://prove2.me/theorems/9fd7e716-8fb6-4bac-a5fc-ea01e820ee69
-- title:
--   Proposition II.1: smooth max-relative entropy regularization
-- statement:
--   Let $H$ be a nonzero finite-dimensional complex Hilbert space and let $\rho\in\mathcal D(H)$ be a normalized density operator. For each positive integer $n$, let $M_n\subseteq\mathcal D(H^{\otimes n})$ be closed and convex. Assume that one fixed full-rank state $\sigma$ has $\sigma^{\otimes n}\in M_n$ for every positive $n$, that every single-copy partial trace preserves the family, that tensor products map $M_n\times M_m$ into $M_{n+m}$, and that conjugation by every copy permutation preserves $M_n$. Define $E_{M_n}(\xi)=\inf_{\omega\in M_n}D_2(\xi\Vert\omega)$, using base-two relative entropy with value $+\infty$ on failed support inclusion, and define $E_M^\infty(\rho)=\inf_{n\ge1}E_{M_n}(\rho^{\otimes n})/n$.
--
--   Put $D_{\max}(\xi\Vert\omega)=\inf\{s\in\mathbb R:\xi\le2^s\omega\}$ and
--   $LR_{M_n}^\epsilon(\xi)=\inf\{D_{\max}(\widetilde\xi\Vert\omega):\widetilde\xi\in\mathcal D(H^{\otimes n}),\ \|\widetilde\xi-\xi\|_1\le\epsilon,\ \omega\in M_n\}$. The ball is closed and contains normalized states only. Then
--   $$
--   \lim_{\epsilon\downarrow0}\liminf_{n\to\infty}\frac{LR_{M_n}^\epsilon(\rho^{\otimes n})}{n}
--   =E_M^\infty(\rho)
--   =\lim_{\epsilon\downarrow0}\limsup_{n\to\infty}\frac{LR_{M_n}^\epsilon(\rho^{\otimes n})}{n}.
--   $$
--
--   Both asymptotic envelopes are retained; the optimization and limits use extended nonnegative values until finiteness follows.
-- source:
--   A Generalization of Quantum Stein's Lemma, arXiv:0904.0281v3, PDF p. 6, Proposition II.1: smooth max-relative entropy regularization

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

/-- PDF p.6 Proposition II.1 Eq.(16): both smoothing identities. -/
theorem smooth_max_regularization {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (M : (n : ℕ) → Set (Mat (Copies I n))) (hM : stateSetAxioms M)
    (rho : Mat I) (hrho : IsDensityMatrix rho) : SmoothFormula M rho := by sorry

end QAlgorithms.Papers.Independent.Intake100.P63

end
