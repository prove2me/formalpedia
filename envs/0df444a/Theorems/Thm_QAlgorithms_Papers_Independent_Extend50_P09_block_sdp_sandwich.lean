-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P09_block_sdp_sandwich
-- name    : QAlgorithms.Papers.Independent.Extend50.P09.block_sdp_sandwich
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:38:15.184818+00:00
-- url     : https://prove2.me/theorems/686443db-3832-4055-bf9f-9f4dd9bd3453
-- title:
--   Lemma 5: block-state SDP sandwich
-- statement:
--   For finite positive-dimensional registers $P,Q$ and a positive operator $X^{PQ}$, write $H_{\min}(P|Q)_X=\sup\{h:\exists\sigma_Q\ge0,\ \operatorname{Tr}\sigma_Q=1,\ X\le2^{-h}I_P\otimes\sigma_Q\}$. The supremum is extended-real, so $H_{\min}(0)=+\infty$; throughout, $-\log_2 0=+\infty$.
--
--   Let $P=P_1P_2$ with all three registers $P_1,P_2,Q$ finite and positive-dimensional. Let $m\ge1$, and let $\Pi_i$ be nonzero self-adjoint orthogonal projections on $P_1$ with pairwise orthogonal ranges. For arbitrary positive operators $\rho_i^{P_2Q}$ put $X=\sum_{i=1}^m\Pi_i\otimes\rho_i$, and define $s(Y)=\inf\{\operatorname{Tr}\sigma:\sigma\ge0,\ I\otimes\sigma\ge Y\}$. Then
--   $$\frac1m\sum_{i=1}^m s(\rho_i)\le s(X)\le\sum_{i=1}^m s(\rho_i).$$
--
--   The nonzero-block convention is required by the source's division by $\operatorname{Tr}\Pi_i$. Neither individual trace-one normalization nor completeness of the block family is added.
-- source:
--   Near-optimal covariant quantum error-correcting codes from random unitaries with symmetries, arXiv:2112.01498v2, PDF p. 17, Lemma 5: block-state SDP sandwich

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P09

noncomputable section

open scoped Matrix Matrix.Norms.Elementwise ComplexConjugate ENNReal ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Extend50.P09

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact generic definitions from the pinned accepted library.

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed bell)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalMinEntropy)

open QAlgorithms.Papers.Independent.Advance50.P02 (negLog)

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P09.covariantMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P09.covariantMatrixBorel

/-- Lemma 5, PDF p.17, (B17), with the nonzero block convention required
by division by Tr Pi_i in (B19). The rho_i are arbitrary PSD operators. -/
theorem block_sdp_sandwich
    {P1 P2 Q : Type*} [Fintype P1] [DecidableEq P1] [Nonempty P1]
    [Fintype P2] [DecidableEq P2] [Nonempty P2]
    [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (m : ℕ) (hm : 0 < m) (Pi : Fin m → Op P1)
    (hself : ∀ i, (Pi i)ᴴ = Pi i) (hidem : ∀ i, Pi i * Pi i = Pi i)
    (hnonzero : ∀ i, Pi i ≠ 0) (horth : ∀ i j, i ≠ j → Pi i * Pi j = 0)
    (rho : Fin m → Op (P2 × Q)) (hpos : ∀ i, (rho i).PosSemidef) :
    let X : Op ((P1 × P2) × Q) := fun a b =>
      ∑ i, Pi i a.1.1 b.1.1 * rho i (a.1.2,a.2) (b.1.2,b.2)
    (∑ i, sdp (rho i)) / m ≤ sdp X ∧ sdp X ≤ ∑ i, sdp (rho i) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P09

end
