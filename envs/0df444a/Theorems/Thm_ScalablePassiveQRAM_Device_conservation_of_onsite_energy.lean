-- Prove2me | Theorems.Thm_ScalablePassiveQRAM_Device_conservation_of_onsite_energy
-- name    : ScalablePassiveQRAM.Device.conservation_of_onsite_energy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:57:50.440757+00:00
-- url     : https://prove2.me/theorems/38377587-2639-48ec-af95-489b94c546fd
-- title:
--   Theorem 6 — Conservation of on-site energy
-- statement:
--   For $n\ge1$, $\Omega>0$, and pinning coefficient $\Delta$, every constructed transition commutes with $P$, and so does $H$. Every computed valid history has the same pinning energy:
--
--   $$[P,T]=[P,H]=0,\qquad P|\Phi_j\rangle=(n+2)\Delta|\Phi_j\rangle.$$
--
--   At $\tau=\pi/\Omega$, the full Hamiltonian $K=H+P$ implements the logical query with common phase $\exp(i\phi_L-i(n+2)\Delta\tau)$ on all input superpositions. This preserves the query time and coherence after pinning is included.
--
--   Differences from the source:
--   - encoding: one-based bit and transition indices and tensor-product register notation → zero-based finite index types and matrices on all physical bit configurations; reason: the finite types enumerate the same modes and every operation is lifted to the full tensor product
--   - reading: unload reverses the load and routing uses the values that can occur on a valid history → unload bits in decreasing order and explicit bit or star flavor sets at every route; reason: the source leaves this schedule implicit; this is the execution described in §§3.1–3.2 and reproduces the layer counts
--   - generalization: positive on-site energy splitting Δ → any real Δ in the exact algebraic pinning and separation identities; reason: commutation, the common eigenvalue, and unitary phase identities are algebraic in Δ and specialize to every physical positive splitting
-- source:
--   Siddhartha Jain, Alexander Dalzell, Connor Hann, STOC 2027 submission #129 (October 2026), Theorem 6, p. 23. Canonical PDF SHA256 725dff5ab83fbe7e163da05440b75cc1d24f83804408cc139eb8954d2f8a076e.

import Definitions.Def_ScalablePassiveQRAM_Device_Energy
import Mathlib

open scoped BigOperators Matrix
set_option synthInstance.maxSize 10000
noncomputable section

namespace ScalablePassiveQRAM.Device
local instance conservation_of_onsite_energyDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance conservation_of_onsite_energyDecidableEq (a : Type) : DecidableEq a := Classical.decEq a

theorem conservation_of_onsite_energy (n : ℕ) (hn : 1 ≤ n) (Ω Δ : ℝ) (hΩ : 0 < Ω) :
    (∀ j, j < length n → ∀ t ∈ transitions n j,
      pinning n Δ * t.operator = t.operator * pinning n Δ) ∧
    pinning n Δ * hamiltonian n Ω = hamiltonian n Ω * pinning n Δ ∧
    (∀ x b D j, j ≤ length n → pinning n Δ *ᵥ history n j x b D =
      ((((n+2 : ℕ) : ℝ)*Δ : ℝ) : ℂ) • history n j x b D) ∧
    evolve (physicalHamiltonian n Ω Δ) (Real.pi/Ω) * endpointEmbedding n 0 =
      Complex.exp (Complex.I * ((phase (length n) - (n+2)*Δ*(Real.pi/Ω) : ℝ) : ℂ)) •
        (endpointEmbedding n (length n) * queryUnitary n) := by sorry

end ScalablePassiveQRAM.Device
