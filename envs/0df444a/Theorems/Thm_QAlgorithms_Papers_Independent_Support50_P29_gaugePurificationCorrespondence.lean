-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P29_gaugePurificationCorrespondence
-- name    : QAlgorithms.Papers.Independent.Support50.P29.gaugePurificationCorrespondence
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T21:16:07.028978+00:00
-- url     : https://prove2.me/theorems/6e5c0004-1fab-4fd9-8966-d544794f1cc7
-- title:
--   Complex representation of the gauge purification
-- statement:
--   Let $s\ge1$, $\hbar>0$, and let $N$ be a Hermitian positive semidefinite $s\times s$ occupation matrix. Put
--   $$
--   \alpha=\hbar\begin{bmatrix}\operatorname{Re}N+I/2&-\operatorname{Im}N\\\operatorname{Im}N&\operatorname{Re}N+I/2\end{bmatrix}.
--   $$
--   Construct $\alpha_{12}$ with the reflected-reference purification formula and let $\Delta_{12}=\operatorname{diag}(\Delta,-\Delta)$, where $\Delta=\hbar\begin{bmatrix}0&I\\-I&0\end{bmatrix}$. Under $C\mapsto\begin{bmatrix}\operatorname{Re}C&-\operatorname{Im}C\\\operatorname{Im}C&\operatorname{Re}C\end{bmatrix}$, together with the explicit permutation from $(q_1;q_2;p_1;p_2)$ to $(q_1;p_1;q_2;p_2)$, one has
--   $$
--   \Delta_{12}^{-1}\alpha_{12}\ \longleftrightarrow\
--   \begin{bmatrix}i(N+I/2)&\sqrt{N^2+N}\\\sqrt{N^2+N}&-i(N+I/2)\end{bmatrix}.
--   $$
--   The square root is the nonnegative spectral square root. This algebraic representation includes zero occupation; no ordinary-density P integral at singular $N$ is asserted. It makes the purification available for the subsequent one-mode channel calculation.
-- source:
--   Sending Quantum Information with Gaussian States, arXiv:quant-ph/9809022v1, PDF p. 8, §3, equation (3.8): complex representation of gauge-invariant purification

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P29

noncomputable section

open Filter

open scoped BigOperators ENNReal Topology ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Support50.P29

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma complexify)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity rankOne productCoeff tensorApply IsTraceClassChannel)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)

open QAlgorithms.Papers.Independent.Frontier30.P10 (WeylSystem)

open QAlgorithms.Papers.Independent.Frontier30.P14 (partialRight PureDensity)

open QAlgorithms.Papers.Independent.Claimed50.P35
  (tracePair thermalInput thermalPurificationDensity vacuumChannel exchangeMatrix RealizedDensity)

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Information100.P49 (thermalEntropy)

/-- Holevo quant-ph/9809022v1, PDF pp.7-8, (3.8): exact complex
representation after the explicit middle-block shuffle. Positive semidefinite
occupation is enough: no ordinary Lebesgue P-density integral is asserted
at singular N, and the vacuum boundary is retained. -/
theorem gaugePurificationCorrespondence (s : ℕ) (hs : 0 < s)
    (hbar : ℝ) (hhbar : 0 < hbar) (N : Matrix (Fin s) (Fin s) ℂ)
    (hN : N.PosSemidef) :
    (reflectedDelta s hbar)⁻¹ * purificationCovariance hbar (gaugeCovariance hbar N) =
      (realify (gaugePurificationMatrix N)).submatrix shuffle shuffle := by sorry

end QAlgorithms.Papers.Independent.Support50.P29

end
