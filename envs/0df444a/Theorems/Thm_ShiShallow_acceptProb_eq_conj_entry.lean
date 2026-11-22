-- Prove2me | Theorems.Thm_ShiShallow_acceptProb_eq_conj_entry
-- name    : ShiShallow.acceptProb_eq_conj_entry
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T05:54:08.406437+00:00
-- url     : https://prove2.me/theorems/69ec2110-bad9-471c-a273-15482616c2e3
-- title:
--   Acceptance probability is a diagonal entry of the conjugated observable
-- statement:
--   acceptProb equals the (x₀, x₀) entry of Uᴴ P U, where U is the circuit matrix, P the output projector and x₀ the padded input. This is the Heisenberg-picture reformulation.
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
import Definitions.Def_ShiShallow_Operator
import Theorems.Thm_ShiShallow_IsLocal_conjTranspose
import Theorems.Thm_ShiShallow_mulVec_inputState
import Theorems.Thm_ShiShallow_ofReal_norm_sq
import Theorems.Thm_ShiShallow_runLayered_eq_mulVec

section
open ShiShallow

theorem ShiShallow.acceptProb_eq_conj_entry {n m : ℕ} (c : Layered (n + m)) (x : Bits n)
    (out : Fin (n + m)) :
    ((acceptProb c x out : ℝ) : ℂ)
      = ((circMatrix c).conjTranspose * projOut out * circMatrix c) (padIn x) (padIn x) := by sorry

end
