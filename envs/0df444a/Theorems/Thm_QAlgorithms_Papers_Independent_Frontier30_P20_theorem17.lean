-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P20_theorem17
-- name    : QAlgorithms.Papers.Independent.Frontier30.P20.theorem17
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:47:49.364834+00:00
-- url     : https://prove2.me/theorems/f889cae4-a60d-4672-87f3-cd27b3376f27
-- title:
--   Theorem 17 (Reduction to normal form)
-- statement:
--   All maps act complex-linearly on the same matrix algebra $M_d(\mathbb C)$, where $d\ge1$. Composition $AB$ applies $B$ first. Norms of maps are induced by the unnormalized Hilbert–Schmidt norm. Choose the positive TP or CPTP class $\mathcal T$. Suppose $T,R\in\mathcal T$ and $T=ARB$, with invertible single-Kraus CP filters $A,B$. Then
--
--   $$T\in\overline{\mathcal I_{\mathcal T}}\iff R\in\overline{\mathcal I_{\mathcal T}}.$$
--
--   The set $\mathcal I_{\mathcal T}$ uses exact products of arbitrarily identity-close factors from the chosen class. The filters need not preserve trace. This reduction preserves infinitesimal divisibility, including singular limits.
-- source:
--   Dividing Quantum Channels, arXiv:math-ph/0611057v3, PDF p. 15, Theorem 17 (Reduction to normal form)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P20

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P20

open QAlgorithms.Papers.Independent.Information100.P26 (Mat outer)

open QAlgorithms.Papers.Independent.Dependency50.P14 (Super)

-- Accepted matrix-unit coordinates on the action of a superoperator.

local notation "coefficients" =>
  QAlgorithms.Papers.Independent.Dependency50.P12.superOfAction

/-- Theorem 17, PDF pp.15--16: filtering preserves infinitesimal divisibility, including closure. -/
theorem theorem17 {d : ℕ} (hd : 0 < d) (completely : Bool) (T R A B : Super d)
    (hT : InClass completely T) (hR : InClass completely R)
    (hA : FilterMap A) (hB : FilterMap B) (hprod : T = A * R * B) :
    Infinitesimal completely T ↔ Infinitesimal completely R := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P20

end
