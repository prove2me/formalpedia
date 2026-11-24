-- Prove2me | Theorems.Thm_P2M_GlobalTheory_BorelAlg_minor_isRelPrime__ca4173270435
-- name    : P2M_GlobalTheory_BorelAlg_minor_isRelPrime__ca4173270435
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:50.033207+00:00
-- url     : https://prove2.me/theorems/7495f8ad-7914-4c28-8782-40bced94361f
-- title:
--   P2 M Global Theory Borel Alg minor is Rel Prime  ca4173270435: P2 M Global Theory Borel Alg minor is Rel Prime  ca4173270435
-- statement:
--   The P2 M Global Theory Borel Alg minor is Rel Prime  ca4173270435 construction uses the P2 M Global Theory Borel Alg minor is Rel Prime  ca4173270435 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsIsHomogeneousOfEquivariant.lean#L26-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsIsHomogeneousOfEquivariant.lean#L26-L38

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IrreducibleDetOfIsRelPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsHomogeneousOfEquivariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.BorelAlg

theorem P2M_GlobalTheory_BorelAlg_minor_isRelPrime__ca4173270435 {R σ : Type*} [CommRing R] [IsDomain R] {k : ℕ}
    (e : Fin k × Fin k → σ) (he : Function.Injective e) (l : Fin k) (hl : ∀ i, i ≤ l) :
    ((Matrix.of fun i j : Fin k => (X (e (i, j)) : MvPolynomial σ R)).updateRow l
      (Pi.single l 1)).det ≠ 0 ∧
    IsRelPrime ((Matrix.of fun i j : Fin k => (X (e (i, j)) : MvPolynomial σ R)).updateRow l
      (Pi.single l 1)).det
      (Matrix.of fun i j : Fin k => (X (e (i, j)) : MvPolynomial σ R)).det := by sorry

alias «GlobalTheory».«BorelAlg».«minor_isRelPrime'» := P2M_GlobalTheory_BorelAlg_minor_isRelPrime__ca4173270435
