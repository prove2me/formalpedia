-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P08_twoMode_physicality
-- name    : QAlgorithms.Papers.Independent.Frontier30.P08.twoMode_physicality
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:15:59.240973+00:00
-- url     : https://prove2.me/theorems/ed94bd3a-84b4-407d-9c96-5747ed4f391e
-- title:
--   Two-mode bona fide covariance conditions
-- statement:
--   Let $V=\begin{pmatrix}A&C\\C^T&B\end{pmatrix}$ be a real symmetric $4\times4$ matrix in the order $(q_1,p_1,q_2,p_2)$, and put $\Delta=\det A+\det B+2\det C$. With $\Omega=\begin{pmatrix}0&1\\-1&0\end{pmatrix}\oplus\begin{pmatrix}0&1\\-1&0\end{pmatrix}$ and $\hbar=2$,
--
--   $$V+i\Omega\succeq0\quad\Longleftrightarrow\quad V\succ0,\quad\det V\ge1,\quad\Delta\le1+\det V.$$
--
--   All three conditions on the right are required together. This criterion also covers pure and partially pure covariances; no uncertainty premise is assumed.
-- source:
--   Gaussian Quantum Information, arXiv:1110.3234v1, PDF p. 10, §II.C.3 Eq.(55): two-mode bona fide conditions

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P08

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier30.P08

open scoped BigOperators ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Dependency50.P39 (Fock coherentCoefficient)

/-- PDF p.10, Eq.(55): all three bona fide conditions, including positive
 definiteness, are conjoined. No physicality hypothesis is assumed. -/
theorem twoMode_physicality (V : Matrix (QuadratureIndex 2) (QuadratureIndex 2) ℝ)
    (hVsym : V.transpose = V) :
    quantumCovariance V ↔
      V.PosDef ∧ 1 ≤ V.det ∧ twoModeDelta V ≤ 1 + V.det := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P08

end
