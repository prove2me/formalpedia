-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P02_extreme_ebt_dimension_regimes
-- name    : QAlgorithms.Papers.Independent.Independent1.P02.extreme_ebt_dimension_regimes
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:18:29.872982+00:00
-- url     : https://prove2.me/theorems/6a1b87a9-fb44-4e0d-b277-86e826e617e1
-- title:
--   Theorem 5(D): qubit characterization and higher-dimensional counterexamples
-- statement:
--   The two dimension regimes for extreme EBT maps are:
--
--   $$\operatorname{ext}(\mathrm{EBT}_2)=\{\text{pure-output CQ maps on }M_2\},$$
--
--   whereas, for every integer $d\ge3$, there exists an extreme EBT endomap of $M_d$ that is not CQ.
--
--   The qubit proof is attributed by the paper on page 8 to Ruskai [18], quant-ph/0302032. The paper supplies the higher-dimensional counterexamples, including the qutrit example. The result separates EBT extremality from pure-output CQ structure in higher dimensions.
-- source:
--   General Entanglement Breaking Channels, arXiv:quant-ph/0302031v2, Theorem 5(D): qubit characterization and higher-dimensional counterexamples, PDF p. 7. https://arxiv.org/abs/quant-ph/0302031v2 . PDF SHA-256: b9741af8740a74b5771c71520597f0a6ee2fa27a7ab56de59ddd399c4f49c465.

import Definitions.Def_QAlgorithms_Defs_HolevoMatrixMaps
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P02_Model
set_option autoImplicit false

/-!
# Entanglement Breaking Channels (quant-ph/0302031v2)

All reference factors occur first. General EB uses the separable positive cone;
EBT additionally preserves trace. Proposed source corrections below require
independent source moderation; see MODERATION_NOTES.md in the assigned unit.
-/

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P02



























































/-- Theorem 5(D), PDF p.7, examples pp.8–9,11–12.
The qubit proof is attributed on p.8 to Ruskai [18], quant-ph/0302032. -/
theorem extreme_ebt_dimension_regimes :
    (∀ Phi : Endomorphism 2, Phi ∈ (ebtSet 2).extremePoints ℝ ↔ IsPureCQ Phi) ∧
    ∀ d : ℕ, 3 ≤ d → ∃ Phi : Endomorphism d,
      Phi ∈ (ebtSet d).extremePoints ℝ ∧ ¬ IsCQ Phi := by sorry










end QAlgorithms.Papers.Independent.Independent1.P02
