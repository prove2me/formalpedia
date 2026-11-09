-- Prove2me | Theorems.Thm_ScalablePassiveQRAM_Device_quantum_boundary_energy
-- name    : ScalablePassiveQRAM.Device.quantum_boundary_energy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:56:25.360022+00:00
-- url     : https://prove2.me/theorems/52b2f5dd-73c0-4fc5-8829-e1059ad05cbc
-- title:
--   Corollary 9 — Quantum boundary energy per query
-- statement:
--   For $n\ge1$, $\Omega>0$, $\Delta\ge0$, fixed $D$, and any joint density operator of the device and external encoded ports, execute the actual root swaps and carrier controls. There are $2n+5$ root operations with total device support size $4n+13$. Each operation changes expected device energy by at most $2\|K_{\rm touch}(S_i)\|$, and
--
--   $$\sum_i|\Delta E_i|\le\sum_i2\|K_{\rm touch}(S_i)\|\le(4n+13)(4\Delta+8J_*).$$
--
--   A uniform absolute constant bounds this by $Cn(\Delta+J_*)$. Free evolution under $K_D$ conserves expected device energy for every real time. With fixed per-qubit control cost and bounded $\Delta,J_*$ this is $O(\log N)$ per query. Classical storage and one-time cooling costs are excluded as in the source.
--
--   Differences from the source:
--   - encoding: one-based bit and transition indices and tensor-product register notation → zero-based finite index types and matrices on all physical bit configurations; reason: the finite types enumerate the same modes and every operation is lifted to the full tensor product
--   - reading: unload reverses the load and routing uses the values that can occur on a valid history → unload bits in decreasing order and explicit bit or star flavor sets at every route; reason: the source leaves this schedule implicit; this is the execution described in §§3.1–3.2 and reproduces the layer counts
--   - encoding: O(n(Δ+J_*)) and the proof estimate 2‖K_touch‖ → the per-operation 2‖K_touch(S_i)‖ bound, its sum, and (4n+13)(4Δ+8J_*) before a uniform O bound; reason: there are n+1 two-qubit swaps each way and three three-qubit carrier operations; each touched device qubit contributes at most 2Δ+4J_* to the touching norm
--   - generalization: positive on-site splitting Δ → Δ≥0 in the energy estimate; reason: the same touching-norm estimate also holds at Δ=0
-- source:
--   Siddhartha Jain, Alexander Dalzell, Connor Hann, STOC 2027 submission #129 (October 2026), Corollary 9, p. 30. Canonical PDF SHA256 725dff5ab83fbe7e163da05440b75cc1d24f83804408cc139eb8954d2f8a076e.

import Definitions.Def_ScalablePassiveQRAM_Device_Energy
import Mathlib

open scoped BigOperators Matrix
set_option synthInstance.maxSize 10000
noncomputable section

namespace ScalablePassiveQRAM.Device
local instance quantum_boundary_energyDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance quantum_boundary_energyDecidableEq (a : Type) : DecidableEq a := Classical.decEq a

theorem quantum_boundary_energy :
    (∀ (n : ℕ), 1 ≤ n → ∀ (Ω Δ : ℝ), 0 < Ω → 0 ≤ Δ → ∀ (D : Database n),
      ((rootOperations n).map fun op => (rootSupport n op).card).sum = 4*n+13 ∧
      (rootOperations n).length = 2*n+5 ∧
      touchBudget n Ω Δ D ≤ (4*n+13)*(4*Δ+8*jStar n Ω) ∧
      (∀ (ρ : Op (EnergyBasis n)) (j : Fin (events n).length) (op : RootOperation),
        WildeQIT.IsDensityOperator ρ → (events n)[j] = .boundary op →
        |expectedEnergy n Ω Δ D (energyState n (j.val+1) Ω Δ D ρ) -
          expectedEnergy n Ω Δ D (energyState n j Ω Δ D ρ)| ≤
            2 * spectralNorm (touchHamiltonian n Ω Δ D (rootSupport n op))) ∧
      (∀ ρ : Op (EnergyBasis n), WildeQIT.IsDensityOperator ρ →
        boundaryCost n Ω Δ D ρ ≤ touchBudget n Ω Δ D) ∧
      (∀ (ρ : Op (EnergyBasis n)) (t : ℝ), WildeQIT.IsDensityOperator ρ →
        expectedEnergy n Ω Δ D (extend (conjugate (evolve (sectorHamiltonian n Ω Δ D) t)) ρ) =
          expectedEnergy n Ω Δ D ρ)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (Ω Δ : ℝ), 0 < Ω → 0 ≤ Δ →
      ∀ (D : Database n) (ρ : Op (EnergyBasis n)), WildeQIT.IsDensityOperator ρ →
        boundaryCost n Ω Δ D ρ ≤ C*n*(Δ+jStar n Ω)) := by sorry

end ScalablePassiveQRAM.Device
