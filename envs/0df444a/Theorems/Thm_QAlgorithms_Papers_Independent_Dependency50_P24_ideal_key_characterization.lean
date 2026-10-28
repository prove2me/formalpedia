-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P24_ideal_key_characterization
-- name    : QAlgorithms.Papers.Independent.Dependency50.P24.ideal_key_characterization
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T16:11:35.572976+00:00
-- url     : https://prove2.me/theorems/201e4629-0669-442d-bd4d-55e4d4a6a916
-- title:
--   Theorem 2: ideal-key characterization
-- statement:
--   All spaces are finite dimensional and have positive dimension. A state means a positive semidefinite operator of trace one. The distinguished product basis $B$ is fixed and is used for both twisting and key measurement. Norms are full trace norms, fidelity $F$ is root fidelity, and logarithms are in bits.
--
--   Let $A$ and $B$ each have dimension $d\ge1$, and let $\rho$ be a state on $ABA'B'$. It has $B$-key when every purification gives the uniform, perfectly correlated key independent of Eve after key measurement. Then
--
--   $$\rho\text{ has }B\text{-key}\iff\rho=\frac1d\sum_{i,j}|ii\rangle\langle jj|\otimes U_i\sigma U_j^\dagger.$$
--
--   Here $\sigma$ is a normalized shield state and each $U_i$ is a shield unitary, both existentially quantified. Equivalently $\rho=V(P_d^+\otimes\sigma)V^\dagger$ for a full $B$-twisting $V$, where $P_d^+$ projects onto $d^{-1/2}\sum_i|ii\rangle$. This characterizes ideal key without requiring the shield to be pure.
-- source:
--   General paradigm for distilling classical key from quantum states, arXiv:quant-ph/0506189v2, PDF p. 7, Theorem 2: ideal-key characterization

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

/-- PDF pp.7–9, Theorem 2: ideal B-key iff private form iff twisted basic form.
A basic pdit may have a mixed shield; only its key factor must be pure. -/
theorem ideal_key_characterization {d : ℕ} [NeZero d] {S T : Type*}
    [Fintype S] [Fintype T] [Nonempty S] [Nonempty T]
    (rho : Op (Key d × (S × T))) (hrho : IsDensityMatrix rho) :
    (HasKey rho ↔ IsPrivate rho) ∧
    (IsPrivate rho ↔ ∃ tau : Op (S × T), IsDensityMatrix tau ∧
      ∃ U : Key d → Matrix.unitaryGroup (S × T) ℂ, rho = twist U (basicPrivate tau)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P24

end
