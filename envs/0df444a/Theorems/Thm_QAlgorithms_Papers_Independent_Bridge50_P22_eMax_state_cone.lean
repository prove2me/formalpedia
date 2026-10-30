-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P22_eMax_state_cone
-- name    : QAlgorithms.Papers.Independent.Bridge50.P22.eMax_state_cone
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:14:51.581303+00:00
-- url     : https://prove2.me/theorems/60cb90f3-3911-4c6f-b277-235af28b7aa5
-- title:
--   Attained separable-cone expression for state Emax
-- statement:
--   Let $\rho_{AB}$ be a density operator on positive finite-dimensional complex registers. Let $\overrightarrow{\mathrm{SEP}}(A:B)$ be the cone of finite sums of tensor products of local positive semidefinite operators, with no trace normalization. Write $E_{\max}(A;B)_\rho=\inf_{\sigma\in\mathrm{SEP}(A:B)}D_{\max}(\rho\Vert\sigma)$, where $\mathrm{SEP}(A:B)$ denotes separable density operators and $D_{\max}$ is the max-relative entropy in bits. The following minimum is attained, and
--
--   $$E_{\max}(A;B)_\rho=\log_2 W_{\mathrm{sep}}(A;B)_\rho,\qquad W_{\mathrm{sep}}(A;B)_\rho=\min\{\operatorname{Tr}X:X\in\overrightarrow{\mathrm{SEP}}(A:B),\ \rho\le X\}.$$
--
--   The inequalities are Loewner inequalities. This expression replaces optimization over normalized comparison states by a cone optimization whose trace objective may exceed one.
-- source:
--   Amortization does not enhance the max-Rains information of a quantum channel, arXiv:1709.04907v2, PDF p. 13, Lemma 6 / eqs. (70)–(71)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P22

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P22

open QAlgorithms QAlgorithms.Entanglement Filter Topology

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P35 (tr elog maxRelative)

open QAlgorithms.Papers.Independent.Support50.P21 (Le eMax)

open QAlgorithms.Papers.Independent.Dependency50.P36 (pptPrime target)

open QAlgorithms.Papers.Independent.Dependency50.P09 (tensorAction)

open QAlgorithms.Papers.Independent.Information100.P04 (IsPPTChannel)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

section Statements

variable {A B C D L R : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype L] [Fintype R]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

variable [DecidableEq L] [DecidableEq R]

variable [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] [Nonempty L] [Nonempty R]

/-- Lemma 6, PDF p.13, (70)–(71): separable-cone state expression with an
attained minimum. X in the optimization need not have trace one. -/
theorem eMax_state_cone (rho : Mat (A × B)) (hrho : IsDensityMatrix rho) :
    eMax rho = elog (wSep rho) ∧ IsLeast (stateConeObjectives rho) (wSep rho) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Bridge50.P22

end
