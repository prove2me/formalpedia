-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P63_generalized_stein
-- name    : QAlgorithms.Papers.Independent.Intake100.P63.generalized_stein
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:14:09.419172+00:00
-- url     : https://prove2.me/theorems/b1f45f55-c839-4483-8dca-9482f6db9e7e
-- title:
--   Theorem I: generalized state-set quantum Stein lemma, direct and strong converse
-- statement:
--   Let $H$ be a nonzero finite-dimensional complex Hilbert space and let $\rho\in\mathcal D(H)$ be a normalized density operator. For each positive integer $n$, let $M_n\subseteq\mathcal D(H^{\otimes n})$ be closed and convex. Assume that one fixed full-rank state $\sigma$ has $\sigma^{\otimes n}\in M_n$ for every positive $n$, that every single-copy partial trace preserves the family, that tensor products map $M_n\times M_m$ into $M_{n+m}$, and that conjugation by every copy permutation preserves $M_n$. Define $E_{M_n}(\xi)=\inf_{\omega\in M_n}D_2(\xi\Vert\omega)$, using base-two relative entropy with value $+\infty$ on failed support inclusion, and define $E_M^\infty(\rho)=\inf_{n\ge1}E_{M_n}(\rho^{\otimes n})/n$.
--
--   For a two-outcome effect $0\le A_n\le I$, set $\alpha_n=\operatorname{Tr}[(I-A_n)\rho^{\otimes n}]$ and $b_n(\omega)=-\log_2\operatorname{Tr}(A_n\omega)/n$, with $-\log_2 0=+\infty$.
--
--   For every $\eta>0$ there is one effect sequence, chosen before the alternatives, such that
--   $$
--   \alpha_n\longrightarrow0,\qquad b_n(\omega_n)+\eta\ge E_M^\infty(\rho)\quad(\forall n\ge1,\ \forall\omega_n\in M_n).
--   $$
--   Conversely, for every $\eta>0$ and every effect sequence satisfying
--   $$
--   b_n(\omega_n)-\eta\ge E_M^\infty(\rho)\quad(\forall n\ge1,\ \forall\omega_n\in M_n),
--   $$
--   one has $\alpha_n\longrightarrow1$.
--
--   This gives the direct and strong-converse operational meaning of the regularized state-set relative entropy.
-- source:
--   A Generalization of Quantum Stein's Lemma, arXiv:0904.0281v3, PDF p. 5, Theorem I: generalized state-set quantum Stein lemma, direct and strong converse

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

/-- PDF p.5 Theorem I, Eqs.(11)--(14): direct and strong-converse clauses. -/
theorem generalized_stein {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (M : (n : ℕ) → Set (Mat (Copies I n))) (hM : stateSetAxioms M)
    (rho : Mat I) (hrho : IsDensityMatrix rho) : SteinClauses M rho := by sorry

end QAlgorithms.Papers.Independent.Intake100.P63

end
