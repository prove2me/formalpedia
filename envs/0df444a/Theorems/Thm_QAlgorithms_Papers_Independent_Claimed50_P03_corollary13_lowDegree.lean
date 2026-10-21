-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P03_corollary13_lowDegree
-- name    : QAlgorithms.Papers.Independent.Claimed50.P03.corollary13_lowDegree
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T08:59:20.212888+00:00
-- url     : https://prove2.me/theorems/aedba4d9-c37e-429d-8e17-2c8d05ce7112
-- title:
--   Corollary 13 (Low-degree approximation)
-- statement:
--   Let $\mathcal D$ be a Borel probability law on normalized $n$-qubit density matrices, invariant under Hadamard and phase gates on each wire independently. Discrete and entangled-state laws are allowed. For a subsystem $S$, define $\gamma^*(\rho_S)=2^{-|S|}\sum_{Q\in\{X,Y,Z\}^{\otimes S}}\operatorname{tr}(Q\rho_S)^2$, with $\gamma^*(\rho_\varnothing)=1$. For a phase-free Pauli $P$, write $\beta_{\mathcal D}(P)=(2/3)^{|P|}\mathbb E_{\mathcal D}\gamma^*(\rho_{\operatorname{supp}P})$.
--
--   For any Hermitian $O=\sum_P\alpha_PP$ and integer $k>0$, define the strict truncation $O^{(<k)}=\sum_{|P|<k}\alpha_PP$. Then
--   $$\mathbb E_{\rho\sim\mathcal D}|\operatorname{tr}(O\rho)-\operatorname{tr}(O^{(<k)}\rho)|^2\le(2/3)^k\|O\|^2.$$
--   The cutoff is strict, unlike the later learning theorems' inclusive truncation. This gives exponential suppression of the high-weight tail.
-- source:
--   Learning to predict arbitrary quantum processes, arXiv:2210.14894v3, PDF p. 37, Corollary 13 (Low-degree approximation)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace

/-- Corollary 13, paper p.37, D14: the strict weight cutoff |P|<k. -/
theorem corollary13_lowDegree (n k : ℕ) (hk : 0 < k) (O : (Matrix (Qubits n) (Qubits n) ℂ))
    (hO : O.IsHermitian) (D : Measure ((Matrix (Qubits n) (Qubits n) ℂ)))
    (hD : IsStateLaw D) (hflat : IsLocallyFlat D) :
    (∫ rho, |effectProb O rho - effectProb (truncateStrict k O) rho| ^ 2 ∂D) ≤
      (2 / 3 : ℝ) ^ k * specNorm O ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P03

end
