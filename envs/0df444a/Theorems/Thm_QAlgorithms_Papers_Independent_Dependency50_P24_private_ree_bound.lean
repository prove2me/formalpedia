-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P24_private_ree_bound
-- name    : QAlgorithms.Papers.Independent.Dependency50.P24.private_ree_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:13:09.178985+00:00
-- url     : https://prove2.me/theorems/d0d2c170-8dea-4909-a8b6-46c827f5b3d0
-- title:
--   Theorem 3: REE of private states
-- statement:
--   All spaces are finite dimensional and have positive dimension. A state means a positive semidefinite operator of trace one. The distinguished product basis $B$ is fixed and is used for both twisting and key measurement. Norms are full trace norms, fidelity $F$ is root fidelity, and logarithms are in bits.
--
--   Let $\gamma$ be a standard-basis private $d$-dit and put $\rho_i=d\langle ii|\gamma|ii\rangle$, its conditional shield state. Let $E_r$ denote relative entropy of entanglement in bits, with infinity for a support violation. Then
--
--   $$E_r^{AA':BB'}(\gamma)\le\log_2 d+\frac1d\sum_{i=0}^{d-1}E_r^{A':B'}(\rho_i).$$
--
--   The shield states are constructed from $\gamma$. This separates the key contribution from conditional shield entanglement.
-- source:
--   General paradigm for distilling classical key from quantum states, arXiv:quant-ph/0506189v2, PDF p. 11, Theorem 3: REE of private states

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

/-- PDF pp.11–12, Theorem 3: conditional shields are constructed from gamma. -/
theorem private_ree_bound {d : ℕ} [NeZero d] {S T : Type*}
    [Fintype S] [Fintype T] [Nonempty S] [Nonempty T]
    (gamma : Op (Key d × (S × T))) (hgamma : IsPrivate gamma) :
    relativeEntanglement (partyCut gamma) ≤ ENNReal.ofReal (logBits d) +
      (d : ℝ≥0∞)⁻¹ * ∑ i, relativeEntanglement (conditionalShield gamma i) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P24

end
