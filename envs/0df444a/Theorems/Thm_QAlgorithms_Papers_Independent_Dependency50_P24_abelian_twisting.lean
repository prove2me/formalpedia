-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P24_abelian_twisting
-- name    : QAlgorithms.Papers.Independent.Dependency50.P24.abelian_twisting
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:27:33.421134+00:00
-- url     : https://prove2.me/theorems/234eeafe-eb25-45fc-b20d-0a2b4de13d7a
-- title:
--   §VI-A: shieldless perfect and approximate key
-- statement:
--   All spaces are finite dimensional and have positive dimension. A state means a positive semidefinite operator of trace one. The distinguished product basis $B$ is fixed and is used for both twisting and key measurement. Norms are full trace norms, fidelity $F$ is root fidelity, and logarithms are in bits.
--
--   For a two-qubit state $\rho$, define $U_\theta=\sum_{ij}e^{i\theta_{ij}}|ij\rangle\langle ij|$. Then
--
--   $$\rho\text{ has computational-basis key}\iff\rho=U_\theta P^+U_\theta^\dagger\text{ for some real phases }\theta.$$
--
--   Moreover, for every $\epsilon>0$, if $|\rho_{00,11}|>1/2-\epsilon$, then some such phases satisfy
--
--   $$F(\rho,U_\theta P^+U_\theta^\dagger)^2\ge1-2\epsilon.$$
--
--   The phases are chosen to align the corner coherence. This characterizes perfect shieldless key and quantifies its approximation.
-- source:
--   General paradigm for distilling classical key from quantum states, arXiv:quant-ph/0506189v2, PDF p. 14, §VI-A: shieldless perfect and approximate key

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

/-- PDF pp.14–15, §VI-A: exact shieldless key and phase-aligned approximate fidelity.
Eq.(93) is an upper bound for arbitrary phases; the lower bound needs an existential phase. -/
theorem abelian_twisting (rho : Op (Key 2)) (hrho : IsDensityMatrix rho) :
    (HasKey (singletonShield rho) ↔ ∃ theta : Key 2 → ℝ, rho = phaseBell theta) ∧
    (∀ eps : ℝ, 0 < eps → ‖rho (0,0) (1,1)‖ > 1/2-eps →
      ∃ theta : Key 2 → ℝ, (rootFidelity rho (phaseBell theta))^2 ≥ 1-2*eps) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P24

end
