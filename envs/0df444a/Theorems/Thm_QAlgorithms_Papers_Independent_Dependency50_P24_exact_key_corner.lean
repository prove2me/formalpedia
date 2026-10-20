-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P24_exact_key_corner
-- name    : QAlgorithms.Papers.Independent.Dependency50.P24.exact_key_corner
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:28:53.447849+00:00
-- url     : https://prove2.me/theorems/b81e93c4-e1aa-4a92-a21e-1bb5deb3df19
-- title:
--   §VI-B: exact key from the corner-block norm
-- statement:
--   All spaces are finite dimensional and have positive dimension. A state means a positive semidefinite operator of trace one. The distinguished product basis $B$ is fixed and is used for both twisting and key measurement. Norms are full trace norms, fidelity $F$ is root fidelity, and logarithms are in bits.
--
--   Let $|\psi\rangle$ purify a state $\rho$ with two-qubit key, let $A_{00,11}=\langle00|\rho|11\rangle$, and let $p_a,\rho_E^a$ be its actual outcome weights and conditional Eve states. Then
--
--   $$\rho\text{ has }B\text{-key}\iff\|A_{00,11}\|_1=\tfrac12\iff\bigl(p_{00}=p_{11}=\tfrac12\text{ and }\rho_E^{00}=\rho_E^{11}\bigr).$$
--
--   Zero-weight conditional states can be chosen arbitrarily and normalized; the displayed equalities force both relevant weights to be nonzero. This is the exact corner-block security criterion.
-- source:
--   General paradigm for distilling classical key from quantum states, arXiv:quant-ph/0506189v2, PDF p. 16, §VI-B: exact key from the corner-block norm

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P24

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Finset

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Accepted declarations are imported rather than redeclared locally.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P04 (bellProjector)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits relativeEntanglement)

/-- PDF p.16, Eq.(100): the printed p00+p11=1/2 is corrected to p00=p11=1/2,
as forced by p.15 and the equality in Eq.(100). -/
theorem exact_key_corner {S T E : Type*} [Fintype S] [Fintype T] [Fintype E]
    [Nonempty S] [Nonempty T] [Nonempty E]
    (psi : EuclideanSpace ℂ ((Key 2 × (S × T)) × E)) (hpsi : IsState psi) :
    (HasKey (traceRight (pureDensity psi)) ↔
      traceNorm (keyBlock (traceRight (pureDensity psi)) (0,0) (1,1)) = 1/2) ∧
    (traceNorm (keyBlock (traceRight (pureDensity psi)) (0,0) (1,1)) = 1/2 ↔
      outcomeWeight psi (0,0) = 1/2 ∧ outcomeWeight psi (1,1) = 1/2 ∧
      conditionalEve psi (0,0) = conditionalEve psi (1,1)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P24

end
