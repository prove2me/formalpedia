-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P20_corollary9
-- name    : QAlgorithms.Papers.Independent.Frontier30.P20.corollary9
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:38:21.665874+00:00
-- url     : https://prove2.me/theorems/0c25ba5c-0445-4d34-bcb0-1556474f18e7
-- title:
--   Corollary 9 (Indivisible positive maps)
-- statement:
--   All maps act complex-linearly on the same matrix algebra $M_d(\mathbb C)$, where $d\ge1$. Composition $AB$ applies $B$ first. Norms of maps are induced by the unnormalized Hilbert–Schmidt norm. If $\lfloor d/2\rfloor$ is odd, transposition $\theta(\rho)=\rho^T$ is positive, trace preserving and indivisible:
--
--   $$\theta=AB,\ A,B\text{ positive TP}\quad\Longrightarrow\quad A\text{ or }B\text{ is a unitary conjugation}.$$
--
--   The ambient class is positive TP maps, as transposition need not be completely positive.
-- source:
--   Dividing Quantum Channels, arXiv:math-ph/0611057v3, PDF p. 11, Corollary 9 (Indivisible positive maps)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P20

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P20

open QAlgorithms.Papers.Independent.Information100.P26 (Mat outer)

open QAlgorithms.Papers.Independent.Dependency50.P14 (Super)

-- Accepted matrix-unit coordinates on the action of a superoperator.

local notation "coefficients" =>
  QAlgorithms.Papers.Independent.Dependency50.P12.superOfAction

/-- Corollary 9, PDF p.11: positive TP indivisibility, with floor(d/2) odd. -/
theorem corollary9 {d : ℕ} (hd : 0 < d) (hodd : Odd (d / 2)) :
    Indivisible false (continuousTranspose d) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P20

end
