-- Prove2me | Theorems.Thm_ShiShallow_isLocal_conj_layer
-- name    : ShiShallow.isLocal_conj_layer
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T05:53:20.965587+00:00
-- url     : https://prove2.me/theorems/7dd44f22-95c7-4366-a88e-de750cbd3c0d
-- title:
--   One layer moves the support by exactly one cone step
-- statement:
--   Conjugating an S-local observable by a layer with pairwise disjoint supports yields an operator local to coneStep l S: gates meeting S enlarge the support, gates missing it cancel.
-- source:
--   Original work by Yueheng Shi (Apache-2.0), formalised in Lean 4 with Mathlib. Part of the ShiShallow development on shallow quantum circuits and causal cones.

/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

Shallow quantum circuits and causal cones.

MODIFICATIONS made for publication on Prove2me: the enclosing `namespace` is replaced by `section`+`open` and the proof is replaced by `sorry`;
no statement or proof was otherwise altered.

Built against Mathlib (Apache-2.0) at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Definitions.Def_ShiShallow_Circuit
import Definitions.Def_ShiShallow_Cone
import Definitions.Def_ShiShallow_Operator
import Theorems.Thm_ShiShallow_IsLocal_conjTranspose
import Theorems.Thm_ShiShallow_conj_eq_of_disjoint
import Theorems.Thm_ShiShallow_conj_mul_eq
import Theorems.Thm_ShiShallow_disjoint_coneStep
import Theorems.Thm_ShiShallow_gateMatrix_unitary
import Theorems.Thm_ShiShallow_isLocal_conj
import Theorems.Thm_ShiShallow_isLocal_gateMatrix

section
open ShiShallow

theorem ShiShallow.isLocal_conj_layer {n : ℕ} (l : List (Instr n)) (hl : LayerOk l)
    {S : Finset (Fin n)} {A : Op n} (hA : IsLocal S A) :
    IsLocal (coneStep l S) ((layerMatrix l).conjTranspose * A * layerMatrix l) := by sorry

end
