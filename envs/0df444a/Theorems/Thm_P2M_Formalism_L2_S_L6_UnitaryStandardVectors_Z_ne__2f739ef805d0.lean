-- Prove2me | Theorems.Thm_P2M_Formalism_L2_S_L6_UnitaryStandardVectors_Z_ne__2f739ef805d0
-- name    : P2M_Formalism_L2_S_L6_UnitaryStandardVectors_Z_ne__2f739ef805d0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:05:58.530475+00:00
-- url     : https://prove2.me/theorems/dc3c769f-49c9-4bca-a565-3535fdad6d3e
-- title:
--   P2 M Formalism L2 S L6 Unitary Standard Vectors Z ne  2f739ef805d0: P2 M Formalism L2 S L6 Unitary Standard Vectors Z ne  2f739ef805d0
-- statement:
--   The P2 M Formalism L2 S L6 Unitary Standard Vectors Z ne  2f739ef805d0 construction uses the P2 M Formalism L2 S L6 Unitary Standard Vectors Z ne  2f739ef805d0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/ZeroOfBlk.lean#L72-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/ZeroOfBlk.lean#L72-L72

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ZeroOfBlk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.L6 Formalism.L2.S.L6.UnitaryStandardVectors
variable {m : ℕ}
variable (π : Fin m → Fin m) (hπ : ∀ a, π (π a) = a) (Z : Matrix (Fin m) (Fin m) ℂ)
  (hZ : ∀ c b, Z c b ≠ 0 ↔ c = π b)
include hπ hZ

theorem P2M_Formalism_L2_S_L6_UnitaryStandardVectors_Z_ne__2f739ef805d0 (i : Fin m) : Z i (π i) ≠ 0 := by sorry

alias «Formalism».«L2».«S».«L6».«UnitaryStandardVectors».«Z_ne'» := P2M_Formalism_L2_S_L6_UnitaryStandardVectors_Z_ne__2f739ef805d0
