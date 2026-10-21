-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P24_privacy_squeezing
-- name    : QAlgorithms.Papers.Independent.Dependency50.P24.privacy_squeezing
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T16:10:01.73499+00:00
-- url     : https://prove2.me/theorems/de956419-71c6-4cf2-9adb-cfd2ec6c4095
-- title:
--   Lemma 2: privacy squeezing
-- statement:
--   All spaces are finite dimensional and have positive dimension. A state means a positive semidefinite operator of trace one. The distinguished product basis $B$ is fixed and is used for both twisting and key measurement. Norms are full trace norms, fidelity $F$ is root fidelity, and logarithms are in bits.
--
--   Let $\rho$ be a state with a two-qubit key and shield $A'B'$, and let $A_{ab}=\langle a|\rho|b\rangle$ be its shield blocks, for $a,b\in\{00,01,10,11\}$. There exists a $B$-twisting $U$ such that
--
--   $$[\operatorname{Tr}_{A'B'}(U\rho U^\dagger)]_{00,11}=\|A_{00,11}\|_1.$$
--
--   The entry is the indicated nonnegative real number. This is an existential global twisting used in privacy squeezing.
-- source:
--   General paradigm for distilling classical key from quantum states, arXiv:quant-ph/0506189v2, PDF p. 6, Lemma 2: privacy squeezing

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

/-- PDF p.6, Lemma 2: existential nonlocal twisting; no LOCC implementation claimed. -/
theorem privacy_squeezing {S T : Type*} [Fintype S] [Fintype T] [Nonempty S] [Nonempty T]
    (rho : Op (Key 2 × (S × T))) (hrho : IsDensityMatrix rho) :
    ∃ U : Key 2 → Matrix.unitaryGroup (S × T) ℂ,
      traceRight (twist U rho) (0,0) (1,1) = (traceNorm (keyBlock rho (0,0) (1,1)) : ℂ) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P24

end
