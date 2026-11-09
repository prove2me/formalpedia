-- Prove2me | Theorems.Thm_ScalablePassiveQRAM_Device_invariant_transfer_chains
-- name    : ScalablePassiveQRAM.Device.invariant_transfer_chains
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:56:19.407221+00:00
-- url     : https://prove2.me/theorems/47e1e2fd-4a22-496d-8c55-61853207f602
-- title:
--   Proposition 1 — Invariant transfer chains
-- statement:
--   Fix $n\ge1$, $\Omega>0$, address $x$, initial bus bit $b$, and memory $D$. Let $V|j\rangle=|\Phi_j(x,b,D)\rangle$ be the computed history embedding. Then
--
--   $$V^\dagger V=I,\qquad HV=VH_{\rm path}.$$
--
--   Thus its range is invariant under the full physical Hamiltonian, and the restriction is exactly the weighted nearest-neighbor path operator of equations (25)–(26). The isometry clause identifies the source's orthonormal history basis rather than assuming it.
--
--   Differences from the source:
--   - encoding: one-based bit and transition indices and tensor-product register notation → zero-based finite index types and matrices on all physical bit configurations; reason: the finite types enumerate the same modes and every operation is lifted to the full tensor product
--   - reading: unload reverses the load and routing uses the values that can occur on a valid history → unload bits in decreasing order and explicit bit or star flavor sets at every route; reason: the source leaves this schedule implicit; this is the execution described in §§3.1–3.2 and reproduces the layer counts
-- source:
--   Siddhartha Jain, Alexander Dalzell, Connor Hann, STOC 2027 submission #129 (October 2026), Proposition 1, p. 18. Canonical PDF SHA256 725dff5ab83fbe7e163da05440b75cc1d24f83804408cc139eb8954d2f8a076e.

import Definitions.Def_ScalablePassiveQRAM_Device_Energy
import Mathlib

open scoped BigOperators Matrix
set_option synthInstance.maxSize 10000
noncomputable section

namespace ScalablePassiveQRAM.Device
local instance invariant_transfer_chainsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance invariant_transfer_chainsDecidableEq (a : Type) : DecidableEq a := Classical.decEq a

theorem invariant_transfer_chains (n : ℕ) (hn : 1 ≤ n) (Ω : ℝ) (hΩ : 0 < Ω)
    (x : Address n) (b : Bool) (D : Database n) :
    (historyEmbedding n x b D).conjTranspose * historyEmbedding n x b D = 1 ∧
    hamiltonian n Ω * historyEmbedding n x b D =
      historyEmbedding n x b D * pathHamiltonian (length n) Ω := by sorry

end ScalablePassiveQRAM.Device
