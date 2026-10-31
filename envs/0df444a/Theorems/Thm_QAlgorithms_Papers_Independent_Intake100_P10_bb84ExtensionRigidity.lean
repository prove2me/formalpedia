-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P10_bb84ExtensionRigidity
-- name    : QAlgorithms.Papers.Independent.Intake100.P10.bb84ExtensionRigidity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:07:08.878972+00:00
-- url     : https://prove2.me/theorems/277b95aa-ece5-4565-b437-9364612fec95
-- title:
--   Every BB84 extension has a common product Eve state
-- statement:
--   Let $a,x\in\{0,1\}$ and let $B=\mathbb C^2$. Define the four BB84 assemblage blocks by
--
--   $$\hat\rho_B^{0,0}=\tfrac12|0\rangle\langle0|,\quad\hat\rho_B^{1,0}=\tfrac12|1\rangle\langle1|,\quad\hat\rho_B^{0,1}=\tfrac12|+\rangle\langle+|,\quad\hat\rho_B^{1,1}=\tfrac12|-\rangle\langle-|,$$
--
--   where $|\pm\rangle=(|0\rangle\pm|1\rangle)/\sqrt2$. Let $E$ be any quantum system and let $\hat\tau_{BE}^{a,x}$ be any positive trace-class extension satisfying $\operatorname{Tr}_E\hat\tau_{BE}^{a,x}=\hat\rho_B^{a,x}$ for every $a,x$ and $\sum_a\hat\tau_{BE}^{a,x}$ independent of $x$. Then there exists one positive trace-one state $\omega_E$, chosen before all $a,x$, such that
--
--   $$\hat\tau_{BE}^{a,x}=\hat\rho_B^{a,x}\otimes\omega_E\qquad\text{for every }a,x.$$
--
--   This is rigidity against every no-signaling extension, with no product-extension hypothesis and no bound on Eve’s dimension.
-- source:
--   Conditional Mutual Information and Quantum Steering, arXiv:1612.03875v2, PDF p. 4, Unnumbered rigidity, (31)–(42)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P10

noncomputable section

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P10

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClassChannel productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P08
  (PositiveTraceClass operatorTrace partialTraceFirst partialTraceSecond IsQuantumOperation)

open QAlgorithms.Papers.Independent.Renew46.P08 (qcmi)

open QAlgorithms.Papers.Independent.Frontier18.P01 (convexOperatorMixture)

open QAlgorithms.Papers.Independent.Information100.P19 (outer)

/-- Unnumbered BB84 rigidity, PDF pp.4--5, (31)--(42): the common normalized
Eve state is existential AFTER the extension and BEFORE every input/outcome. -/
theorem bb84ExtensionRigidity (E : Type) (r : Extension bb84Assemblage E) :
    ∃ omega : State E, ∀ x a, r.block x a = productCoeff (bb84Assemblage x a) omega.coefficients := by sorry

end QAlgorithms.Papers.Independent.Intake100.P10

end
