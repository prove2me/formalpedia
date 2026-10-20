-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P24_private_bit_x_form
-- name    : QAlgorithms.Papers.Independent.Dependency50.P24.private_bit_x_form
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T16:23:47.37541+00:00
-- url     : https://prove2.me/theorems/694691d5-9918-4c8c-98fa-ccf6d930d37c
-- title:
--   §IV: every private bit has a one-operator form
-- statement:
--   All spaces are finite dimensional and have positive dimension. A state means a positive semidefinite operator of trace one. The distinguished product basis $B$ is fixed and is used for both twisting and key measurement. Norms are full trace norms, fidelity $F$ is root fidelity, and logarithms are in bits.
--
--   An operator $\gamma$ is a private bit in the fixed basis if and only if there exists a shield operator $X$ with $\|X\|_1=1$ such that
--
--   $$\gamma=\frac12\begin{pmatrix}\sqrt{XX^\dagger}&0&0&X\\0&0&0&0\\0&0&0&0\\X^\dagger&0&0&\sqrt{X^\dagger X}\end{pmatrix}.$$
--
--   The square roots are positive semidefinite square roots. This gives a one-operator representation of every private bit.
-- source:
--   General paradigm for distilling classical key from quantum states, arXiv:quant-ph/0506189v2, PDF p. 9, §IV: every private bit has a one-operator form

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

/-- PDF pp.9–10, Eq.(43): one-operator characterization of every fixed-basis pbit. -/
theorem private_bit_x_form {S T : Type*} [Fintype S] [Fintype T]
    [Nonempty S] [Nonempty T] (gamma : Op (Key 2 × (S × T))) :
    IsPrivate gamma ↔ ∃ X : Op (S × T), traceNorm X = 1 ∧ gamma = xForm X := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P24

end
