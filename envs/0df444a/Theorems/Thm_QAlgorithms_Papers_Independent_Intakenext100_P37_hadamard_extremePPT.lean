-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P37_hadamard_extremePPT
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P37.hadamard_extremePPT
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:23:51.019003+00:00
-- url     : https://prove2.me/theorems/c1209691-cfe1-4ee0-9caf-e436c41b129d
-- title:
--   Observation 2: extremality of the particular rho_H
-- statement:
--   Let $\rho_H$ be the specific normalized Hadamard state of Eqs. (9)–(16), on key and shield qubits. Let $\mathcal P$ be the entire convex set of density matrices positive under transposition of $BB'$, expressed in $ABA'B'$ coordinates. The printed claim is
--
--   $$\rho_H\in\operatorname{Ext}(\mathcal P).$$
--
--   This is global extremality among all PPT states on the same physical $4\otimes4$ system. It is stronger than extremality along a single mixture line or boundary membership. The paper's line-only proof is not a verification of the global claim; independent mathematical moderation remains required.
-- source:
--   Low dimensional bound entanglement with one-way distillable cryptographic key, arXiv:quant-ph/0506203v1, PDF p. 3, Observation 2: extremality of the particular rho_H

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P37

noncomputable section

open scoped Matrix BigOperators ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P37

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Dependency50.P24
  (Key IsPrivate xForm twist twistingMatrix associatedCCQ transposeSecond transposeBob partyCut)

/-- PDF p.3, Observation 2: the printed GLOBAL extreme-point claim for the
particular rho_H. Its line-only printed proof does not establish this assertion;
independent mathematical moderation is required. No replacement by boundary membership. -/
theorem hadamard_extremePPT :
    rhoHadamard ∈ Set.extremePoints ℝ (pptSet (a := 2) (b := 2)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P37

end
