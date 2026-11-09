-- Prove2me | Theorems.Thm_ScalablePassiveQRAM_Device_unique_predecessor
-- name    : ScalablePassiveQRAM.Device.unique_predecessor
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:57:18.594959+00:00
-- url     : https://prove2.me/theorems/9077114b-331b-4ff8-b373-65f3327fc4ac
-- title:
--   Lemma 4 — Unique predecessor
-- statement:
--   For $n\ge1$, an address $x$, bus bit $b$, database $D$, and every $1\le j\le L$, exactly one adjoint transition at step $j$ acts nontrivially on the computed branch configuration.
--
--   $$T|\Phi_{j-1}(x,b,D)\rangle=|\Phi_j(x,b,D)\rangle,\qquad T^\dagger|\Phi_j(x,b,D)\rangle=|\Phi_{j-1}(x,b,D)\rangle.$$
--
--   All other adjoints at that step annihilate the configuration. The statement supplies the backward action along the history chain.
--
--   Differences from the source:
--   - encoding: one-based bit and transition indices and tensor-product register notation → zero-based finite index types and matrices on all physical bit configurations; reason: the finite types enumerate the same modes and every operation is lifted to the full tensor product
--   - reading: unload reverses the load and routing uses the values that can occur on a valid history → unload bits in decreasing order and explicit bit or star flavor sets at every route; reason: the source leaves this schedule implicit; this is the execution described in §§3.1–3.2 and reproduces the layer counts
-- source:
--   Siddhartha Jain, Alexander Dalzell, Connor Hann, STOC 2027 submission #129 (October 2026), Lemma 4, p. 18. Canonical PDF SHA256 725dff5ab83fbe7e163da05440b75cc1d24f83804408cc139eb8954d2f8a076e.

import Definitions.Def_ScalablePassiveQRAM_Device_Energy
import Mathlib

open scoped BigOperators Matrix
set_option synthInstance.maxSize 10000
noncomputable section

namespace ScalablePassiveQRAM.Device
local instance unique_predecessorDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance unique_predecessorDecidableEq (a : Type) : DecidableEq a := Classical.decEq a

theorem unique_predecessor (n : ℕ) (hn : 1 ≤ n) (x : Address n) (b : Bool) (D : Database n) :
    ∀ j, j < length n → ∃ t : Fin (transitions n j).length,
      ((transitions n j)[t]).operator *ᵥ history n j x b D = history n (j+1) x b D ∧
      ((transitions n j)[t]).operator.conjTranspose *ᵥ history n (j+1) x b D = history n j x b D ∧
      ∀ u : Fin (transitions n j).length, u ≠ t →
        ((transitions n j)[u]).operator.conjTranspose *ᵥ history n (j+1) x b D = 0 := by sorry

end ScalablePassiveQRAM.Device
