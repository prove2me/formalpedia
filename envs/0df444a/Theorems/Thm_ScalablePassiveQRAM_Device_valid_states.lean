-- Prove2me | Theorems.Thm_ScalablePassiveQRAM_Device_valid_states
-- name    : ScalablePassiveQRAM.Device.valid_states
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:57:07.293146+00:00
-- url     : https://prove2.me/theorems/552c9747-026d-4657-9be4-5b97d7f471e8
-- title:
--   Lemma 3 — Valid states
-- statement:
--   Let $n\ge1$, let $x$ be an address, $b$ an initial bus bit, and $D$ the database. At every scheduled layer $0\le j\le L$, the computed configuration has exactly one active carrier on that layer, every other carrier is vacant, the switch slices and address/bus ports have precisely their scheduled contents, and memory remains $D$.
--
--   $$T|\Phi_j(x,b,D)\rangle=|\Phi_{j+1}(x,b,D)\rangle.$$
--
--   For $j<L$, the next carrier and routing target slice are vacant; exactly one forward term gives this equality and all other forward terms annihilate the state. This fixes the configuration invariants needed to interpret the physical evolution.
--
--   Differences from the source:
--   - encoding: one-based bit and transition indices and tensor-product register notation → zero-based finite index types and matrices on all physical bit configurations; reason: the finite types enumerate the same modes and every operation is lifted to the full tensor product
--   - reading: unload reverses the load and routing uses the values that can occur on a valid history → unload bits in decreasing order and explicit bit or star flavor sets at every route; reason: the source leaves this schedule implicit; this is the execution described in §§3.1–3.2 and reproduces the layer counts
--   - reading: Lemma 3 clause (e) and its successor sentence are printed through j=L → clauses (a)–(d) through j=L and targets and successor for j<L; reason: there is no layer L+1 or transition T_{L+1}; the final configuration remains included
-- source:
--   Siddhartha Jain, Alexander Dalzell, Connor Hann, STOC 2027 submission #129 (October 2026), Lemma 3, p. 17. Canonical PDF SHA256 725dff5ab83fbe7e163da05440b75cc1d24f83804408cc139eb8954d2f8a076e.

import Definitions.Def_ScalablePassiveQRAM_Device_Energy
import Mathlib

open scoped BigOperators Matrix
set_option synthInstance.maxSize 10000
noncomputable section

namespace ScalablePassiveQRAM.Device
local instance valid_statesDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance valid_statesDecidableEq (a : Type) : DecidableEq a := Classical.decEq a

theorem valid_states (n : ℕ) (hn : 1 ≤ n) (x : Address n) (b : Bool) (D : Database n) :
    (∀ j, j ≤ length n →
      (∃ s : Fin 3, ∀ (k : Fin (length n+1)) (v : Address (layerDepth n k)) (c : Fin 3),
        historyConfig n j x b D (.inr (.inl (.inl ⟨k,v,c⟩))) =
          decide (k.val = j ∧ v = (fun i => bits n x i.val) ∧ c = s)) ∧
      (∀ q : Switch n, historyConfig n j x b D (.inr (.inl (.inr q))) = switchContents n j x q) ∧
      (∀ q : Ports n, historyConfig n j x b D (.inl q) = portContents n j x b D q) ∧
      (∀ a : Address n, historyConfig n j x b D (memoryQ n a) = D a)) ∧
    (∀ j, j < length n →
      (∀ c : Fin 3, historyConfig n j x b D (carrierQ n (j+1) (bits n x) c) = false) ∧
      (∀ d down bit, (schedule n)[j]? = some (.route d down bit) →
        ∀ c q, switchQ n d (routeCount n j d+1) (bits n x) c = some q →
          historyConfig n j x b D q = false) ∧
      ∃ t : Fin (transitions n j).length,
        ((transitions n j)[t]).operator *ᵥ history n j x b D = history n (j+1) x b D ∧
        ∀ u : Fin (transitions n j).length, u ≠ t →
          ((transitions n j)[u]).operator *ᵥ history n j x b D = 0) := by sorry

end ScalablePassiveQRAM.Device
