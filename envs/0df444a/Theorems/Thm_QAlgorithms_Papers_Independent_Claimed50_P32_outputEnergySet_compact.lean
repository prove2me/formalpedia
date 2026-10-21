-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P32_outputEnergySet_compact
-- name    : QAlgorithms.Papers.Independent.Claimed50.P32.outputEnergySet_compact
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:27:56.743856+00:00
-- url     : https://prove2.me/theorems/1f668ce5-4420-4f42-9893-190a1819b2e0
-- title:
--   A faithful-state output energy bound gives a compact channel set
-- statement:
--   Let $\sigma$ be a faithful input state, let $G$ be a nonnegative output Hamiltonian with a complete eigenbasis whose eigenvalues have finite sublevel sets, and let $h>0$. Both Hilbert spaces are nonzero and separable. Then
--
--   $$\{\Phi\in\mathfrak F_{=1}:\operatorname{Tr}(G\Phi(\sigma))\leq h\}\text{ is strongly compact}.$$
--
--   Mean energy is an extended nonnegative sum in the eigenbasis. Empty sublevels and finite dimensions are allowed. This compactness result needs no partition-function assumption.
-- source:
--   On approximation of quantum channels, arXiv:0711.2245v1, PDF p. 10, §3, Example 2: compact bounded-output-energy channel set

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P32

noncomputable section

open Filter

open scoped Topology ENNReal NNReal BigOperators

namespace QAlgorithms.Papers.Independent.Claimed50.P32

open QAlgorithms.RealRegisters (Hilbert)

/-- §3, Example 2, PDF p.10: bounded output energy at one faithful state
specifies a strongly compact set of channels. Empty sublevels are allowed;
no partition-function condition is imposed. -/
theorem outputEnergySet_compact {I J : Type}
    [Countable I] [Nonempty I] [Countable J] [Nonempty J] (sigma : Nuclear.State I)
    (hfaithful : Operators.HasFullSupport sigma) (energy : J → ℝ≥0)
    (henergy : IsEnergyOperator energy) (h : ℝ) (hh : 0 < h) :
    IsCompact {Phi : StrongChannel I J |
      spectralMeanEnergy energy (evaluate Phi.val sigma) ≤ ENNReal.ofReal h} := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P32

end
