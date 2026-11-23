-- Prove2me | Theorems.Thm_P2M_GlobalTheory_BorelAlg_irreducible_det__000b129e89d6
-- name    : P2M_GlobalTheory_BorelAlg_irreducible_det__000b129e89d6
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:57.731056+00:00
-- url     : https://prove2.me/theorems/d017f3d4-8890-4e8f-bc23-0205538740e9
-- title:
--   P2 M Global Theory Borel Alg irreducible det  000b129e89d6: P2 M Global Theory Borel Alg irreducible det  000b129e89d6
-- statement:
--   The P2 M Global Theory Borel Alg irreducible det  000b129e89d6 construction uses the P2 M Global Theory Borel Alg irreducible det  000b129e89d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsIsHomogeneousOfEquivariant.lean#L40-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsIsHomogeneousOfEquivariant.lean#L40-L45

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

theorem P2M_GlobalTheory_BorelAlg_irreducible_det__000b129e89d6 {R σ : Type*} [CommRing R] [IsDomain R] {k : ℕ} (hk : k ≠ 0)
    (e : Fin k × Fin k → σ) (he : Function.Injective e) :
    Irreducible (Matrix.of fun i j : Fin k => (X (e (i, j)) : MvPolynomial σ R)).det := by sorry

alias «GlobalTheory».«BorelAlg».«irreducible_det'» := P2M_GlobalTheory_BorelAlg_irreducible_det__000b129e89d6
