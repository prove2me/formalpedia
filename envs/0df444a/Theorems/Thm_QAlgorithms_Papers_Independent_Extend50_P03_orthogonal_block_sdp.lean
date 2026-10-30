-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P03_orthogonal_block_sdp
-- name    : QAlgorithms.Papers.Independent.Extend50.P03.orthogonal_block_sdp
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T12:59:18.663429+00:00
-- url     : https://prove2.me/theorems/d89c97c9-c4e2-40fc-b3e6-2082fbe8fc26
-- title:
--   Lemma 4: orthogonal-block conditional-min-entropy SDP bounds
-- statement:
--   Let $P_1,P_2,Q$ be finite nonempty registers, $m\ge1$, and let $\Pi_i$ be nonzero self-adjoint mutually orthogonal projectors on $P_1$. Let $\rho_i\ge0$ act on $P_2\otimes Q$, with $\rho=\sum_{i=1}^m\Pi_i\otimes\rho_i$ a normalized state. The individual blocks need not be normalized. For $s(X)=\inf\{\operatorname{Tr}\sigma:\sigma\ge0,\ I_P\otimes\sigma\ge X\}$, with the appropriate unconditioned register $P$, one has
--
--   $$\frac1m\sum_{i=1}^m s(\rho_i)\le s(\rho)\le\sum_{i=1}^m s(\rho_i).$$
--
--   No rank-one or completeness assumption is imposed on the projectors. **Source correction:** zero projectors must be omitted, as the printed proof divides by $\operatorname{Tr}\Pi_i$; independent moderation is required.
-- source:
--   Charge-conserving unitaries typically generate optimal covariant quantum error-correcting codes, arXiv:2102.11835v1, PDF p. 19, Lemma 4: orthogonal-block conditional-min-entropy SDP bounds

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P03

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Extend50.P03

open QAlgorithms.Papers.Independent.Support50.P23 (minEntropy)

attribute [local instance] Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P03.matrixContinuousENorm

/-- Lemma 4, PDF p.19 (SDP on p.18): corrected support convention Pi_i≠0.
Printed: disjoint projectors. Changed: omit zero projectors, as the proof divides
by Tr(Pi_i). Blocks remain arbitrary PSD operators, without unit-trace assumptions.
This correction requires independent moderation. -/
theorem orthogonal_block_sdp {P1 P2 Q : Type*}
    [Fintype P1] [Fintype P2] [Fintype Q]
    [DecidableEq P1] [DecidableEq P2] [DecidableEq Q]
    [Nonempty P1] [Nonempty P2] [Nonempty Q]
    {m : ℕ} (hm : 1 ≤ m) (Pi : Fin m → Matrix P1 P1 ℂ)
    (rho : Fin m → Matrix (P2 × Q) (P2 × Q) ℂ)
    (hPi : ∀ i, (Pi i).IsHermitian ∧ Pi i * Pi i = Pi i ∧ Pi i ≠ 0)
    (horth : ∀ i j, i ≠ j → Pi i * Pi j = 0)
    (hrho : ∀ i, (rho i).PosSemidef)
    (hnorm : IsDensityMatrix (orthogonalBlockOperator Pi rho)) :
    (∑ i, minSdp (rho i)) / (m : ℝ) ≤ minSdp (orthogonalBlockOperator Pi rho) ∧
      minSdp (orthogonalBlockOperator Pi rho) ≤ ∑ i, minSdp (rho i) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P03

end
