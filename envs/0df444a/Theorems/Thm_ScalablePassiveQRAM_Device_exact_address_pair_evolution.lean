-- Prove2me | Theorems.Thm_ScalablePassiveQRAM_Device_exact_address_pair_evolution
-- name    : ScalablePassiveQRAM.Device.exact_address_pair_evolution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:02:07.942601+00:00
-- url     : https://prove2.me/theorems/5b592a89-ddb1-4e4e-86fb-4329f4231681
-- title:
--   §4.1, Eq. (58) — Exact evolution of one address pair
-- statement:
--   Fix a classical database $D$, addresses $x,y$, $n\ge1$, $\Omega>0$, and $\Delta$. Let $Z$ be any operator on the bus and a reference of any finite dimension, and let $\omega$ be any operator on auxiliaries outside $F_x\cup F_y$. Prepare the union footprint cleanly, including the initial root carrier, and encode the address block $|x\rangle\langle y|$.
--
--   $$\mathcal D_{AB}\operatorname{tr}_{\rm aux}\!\left[e^{-iK_D\tau}(\mathcal V_{AB}(|x\rangle\langle y|\otimes Z)\otimes|{\rm clean}\rangle\langle{\rm clean}|\otimes\omega)e^{iK_D\tau}\right]=|x\rangle\langle y|\otimes U_xZU_y^\dagger\operatorname{tr}\omega.$$
--
--   Here $\tau=\pi/\Omega$ and $U_x=X^{D_x}$. Neither operator needs to be positive or normalized. This preserves off-diagonal address coherence and arbitrary reference entanglement.
--
--   Differences from the source:
--   - encoding: one-based bit and transition indices and tensor-product register notation → zero-based finite index types and matrices on all physical bit configurations; reason: the finite types enumerate the same modes and every operation is lifted to the full tensor product
--   - reading: unload reverses the load and routing uses the values that can occur on a valid history → unload bits in decreasing order and explicit bit or star flavor sets at every route; reason: the source leaves this schedule implicit; this is the execution described in §§3.1–3.2 and reproduces the layer counts
--   - generalization: positive on-site energy splitting Δ → any real Δ in the exact algebraic pinning and separation identities; reason: commutation, the common eigenvalue, and unitary phase identities are algebraic in Δ and specialize to every physical positive splitting
-- source:
--   Siddhartha Jain, Alexander Dalzell, Connor Hann, STOC 2027 submission #129 (October 2026), §4.1, Eq. (58), p. 28. Canonical PDF SHA256 725dff5ab83fbe7e163da05440b75cc1d24f83804408cc139eb8954d2f8a076e.

import Definitions.Def_ScalablePassiveQRAM_Device_Energy
import Mathlib

open scoped BigOperators Matrix
set_option synthInstance.maxSize 10000
noncomputable section

namespace ScalablePassiveQRAM.Device
local instance exact_address_pair_evolutionDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance exact_address_pair_evolutionDecidableEq (a : Type) : DecidableEq a := Classical.decEq a

theorem exact_address_pair_evolution (n : ℕ) (hn : 1 ≤ n) (Ω Δ : ℝ) (hΩ : 0 < Ω)
    (D : Database n) (x y : Address n) (r : ℕ) (Z : Op (Bool × Fin r))
    (ω : Op (OutsideBasis n x y)) :
    pairOutput n r Ω Δ D (pairInput n r D x y Z ω) =
      (fun i j => if i.1.1 = x ∧ j.1.1 = y then
        Z (xor i.1.2 (D x),i.2) (xor j.1.2 (D y),j.2) * ω.trace else 0) := by sorry

end ScalablePassiveQRAM.Device
