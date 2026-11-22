-- Prove2me | Theorems.Thm_P2M_Formalism_UG_P_mem_stdLat_iff__3723b4f8990e
-- name    : P2M_Formalism_UG_P_mem_stdLat_iff__3723b4f8990e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:17:13.19362+00:00
-- url     : https://prove2.me/theorems/8a72a7bb-a268-451a-a481-eb55f2c6d605
-- title:
--   P2 M Formalism UG P mem std Lat iff  3723b4f8990e: P2 M Formalism UG P mem std Lat iff  3723b4f8990e
-- statement:
--   The P2 M Formalism UG P mem std Lat iff  3723b4f8990e construction uses the P2 M Formalism UG P mem std Lat iff  3723b4f8990e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Stabstd.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Stabstd.lean#L11-L14

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Matrix
variable {A R : Type} [CommRing A] [CommRing R] [Algebra R A] {n : Type} [Fintype n] [DecidableEq n]

theorem P2M_Formalism_UG_P_mem_stdLat_iff__3723b4f8990e (x : n → A) :
    x ∈ stdLat (n := n) (A := A) R ↔ ∀ i, x i ∈ Set.range (algebraMap R A) := by sorry

alias «Formalism».«UG».«P».«mem_stdLat_iff'» := P2M_Formalism_UG_P_mem_stdLat_iff__3723b4f8990e
