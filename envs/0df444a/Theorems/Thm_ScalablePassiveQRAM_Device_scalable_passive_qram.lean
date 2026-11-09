-- Prove2me | Theorems.Thm_ScalablePassiveQRAM_Device_scalable_passive_qram
-- name    : ScalablePassiveQRAM.Device.scalable_passive_qram
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:56:37.604995+00:00
-- url     : https://prove2.me/theorems/513fdf4f-0ccc-4780-8bd0-b4d883d3a3ee
-- title:
--   Main Result 1 — Scalable passive QRAM
-- statement:
--   For every $n\ge1$, the explicit data-independent device with $N=2^n$, $\Omega=1/L$, $\Delta=3$, and $L=2n^2+4n+3$ implements the memory query coherently. It has exactly $51N-18n-36$ physical qubits, locality at most four, degree at most four, and $O(N)$ interaction terms. Every address, bus, and memory superposition has the same global phase. Both $H$ and $K=H+P$ implement the query at $\tau=\pi L=O(n^2)$.
--
--   $$\sum_i|\Delta E_i|\le\sum_i2\|K_{\rm touch}(S_i)\|\le(4n+13)(12+8J_*)\le Cn.$$
--
--   Free evolution conserves energy. The number of root interventions is $O(n)$, and no bulk reset is part of the query. For every $m\ge1$, database, and finite algorithm with arbitrary intervening channels, the separately prepared thermal and static channels satisfy
--
--   $$\epsilon_m^{\rm thermal,retained}\le\min\{2,4m\sqrt{F_ne^{-\beta g}}\},\qquad \epsilon_m^{\rm static}\le\min\{2,2m(m+1)\tau W\},$$
--
--   where $F_n=10n^2+14n+12$, $g=3-\kappa\ge1$, and $W\le(F_n+3n+3)\lambda_{\rm err}$. Thermal error at most $\varepsilon$ follows from $\beta g\ge\log F_n+2\log(4m/\varepsilon)$; the retained ideal output includes the original Gibbs marginal. Uniform asymptotic constants give the $\log\log N+\log(m/\varepsilon)$ inverse-temperature threshold for $n\ge2$, and the stated uniform sufficient temperature bound for polynomial $m,\varepsilon^{-1}$ and a fixed positive gap.
--
--   $$\lambda_{\rm err}\le c\varepsilon/(m^2\log^4N),\qquad \delta\le c\varepsilon/(m^2d_{\rm err}\log^4N)$$
--
--   suffice for static error at most $\varepsilon$; the latter assumes $d_{\rm err}\ge1$. Static errors may have arbitrary supports including memory and the root record. Constants precede all varying device sizes, data, errors, and algorithms. This is Main Result 1's full passive and scalable operational claim, including finite-size bounds and reuse, rather than only noiseless lookup.
--
--   Differences from the source:
--   - encoding: one-based bit and transition indices and tensor-product register notation → zero-based finite index types and matrices on all physical bit configurations; reason: the finite types enumerate the same modes and every operation is lifted to the full tensor product
--   - reading: unload reverses the load and routing uses the values that can occur on a valid history → unload bits in decreasing order and explicit bit or star flavor sets at every route; reason: the source leaves this schedule implicit; this is the execution described in §§3.1–3.2 and reproduces the layer counts
--   - encoding: there exists a scalable device family with Ω=Θ(1/L) and fixed on-site gap → the explicit witness Ω=1/L, Δ=3; reason: the source gives an existence claim; this witness has J_*≤1/2, κ≤10/9 and g≥1
--   - encoding: rectangular unhalved diamond norm of the explicitly constructed channels → the identical density-operator supremum over every finite reference dimension for explicit superoperators, using the published trace norm; reason: this avoids inserting substantive CPTP proofs into definitions; the physical maps are encoding, unitary evolution, partial trace, replacement, and decoding channels
--   - encoding: O(n(Δ+J_*)) and the proof estimate 2‖K_touch‖ → the per-operation 2‖K_touch(S_i)‖ bound, its sum, and (4n+13)(4Δ+8J_*) before a uniform O bound; reason: there are n+1 two-qubit swaps each way and three three-qubit carrier operations; each touched device qubit contributes at most 2Δ+4J_* to the touching norm
--   - encoding: asymptotic log log N bounds → n≥2 for log log N formulas, with exact bounds also stated for n=1; reason: log log 2 is negative; these are asymptotic statements and the finite-size guarantees are kept without narrowing
--   - reading: Theorem 2(ii) names E_D while the schematic equation (4) keeps memory D unchanged → the §4.3 induced channel with the recorded interface and memory traced out, targeting original D; reason: §1.2 says (ii) is proved in §4.3, whose perturbations may flip memory and whose root record is explicit
-- source:
--   Siddhartha Jain, Alexander Dalzell, Connor Hann, STOC 2027 submission #129 (October 2026), Main Result 1, p.4; Theorems 1–2, pp.7–8; Corollaries 9–10, pp.30–31. Canonical PDF SHA256 725dff5ab83fbe7e163da05440b75cc1d24f83804408cc139eb8954d2f8a076e.

import Definitions.Def_ScalablePassiveQRAM_Device_Energy
import Mathlib

open scoped BigOperators Matrix
set_option synthInstance.maxSize 10000
noncomputable section

namespace ScalablePassiveQRAM.Device
local instance goalDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance goalDecidableEq (a : Type) : DecidableEq a := Classical.decEq a

/-- Main Result 1, for the explicit data-independent family Ω=1/L, Δ=3.
Thermal and static clauses use separate preparations and separate output channels. -/
theorem scalable_passive_qram :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    (∀ (n : ℕ), 1 ≤ n →
      length n = 2*n^2+4*n+3 ∧
      Fintype.card (Qubit n) + 18*n+36 = 51*2^n ∧
      (∀ j, j < length n → ∀ t ∈ transitions n j, t.support.card ≤ 4 ∧
        supportedOn n (t.support.image Sum.inr)
          (fun i j => if i.1 = j.1 then fullMatrix n t.operator i.2 j.2 else 0)) ∧
      (∀ q : Qubit n, ((List.range (length n)).map fun j =>
        ((transitions n j).filter fun t => decide (q ∈ t.support)).length).sum ≤ 4) ∧
      ((List.range (length n)).map fun j => (transitions n j).length).sum ≤ C*2^n ∧
      (∀ x : Address n, (footprint n x).card = footprintSize n) ∧
      jStar n ((length n:ℝ)⁻¹) ≤ 1/2 ∧ 1 ≤ 3-kappa n ((length n:ℝ)⁻¹) ∧
      Real.pi*(length n) ≤ C*(n:ℝ)^2 ∧
      evolve (hamiltonian n ((length n:ℝ)⁻¹)) (Real.pi*length n) * endpointEmbedding n 0 =
        Complex.exp (Complex.I * (phase (length n) : ℂ)) •
          (endpointEmbedding n (length n) * queryUnitary n) ∧
      evolve (physicalHamiltonian n ((length n:ℝ)⁻¹) 3) (Real.pi*length n) * endpointEmbedding n 0 =
        Complex.exp (Complex.I * ((phase (length n) - (n+2)*3*(Real.pi*length n) : ℝ) : ℂ)) •
          (endpointEmbedding n (length n) * queryUnitary n) ∧
      (rootOperations n).length ≤ C*n ∧
      (∀ (D : Database n) (ρ : Op (EnergyBasis n)), WildeQIT.IsDensityOperator ρ →
        boundaryCost n ((length n:ℝ)⁻¹) 3 D ρ ≤ touchBudget n ((length n:ℝ)⁻¹) 3 D ∧
        touchBudget n ((length n:ℝ)⁻¹) 3 D ≤ (4*n+13)*(12+8*jStar n ((length n:ℝ)⁻¹)) ∧
        boundaryCost n ((length n:ℝ)⁻¹) 3 D ρ ≤ C*n ∧
        ∀ t : ℝ, expectedEnergy n ((length n:ℝ)⁻¹) 3 D
          (extend (conjugate (evolve (sectorHamiltonian n ((length n:ℝ)⁻¹) 3 D) t)) ρ) =
            expectedEnergy n ((length n:ℝ)⁻¹) 3 D ρ) ∧
      (∀ (D : Database n) (m w : ℕ), 1 ≤ m → ∀ (β : ℝ) (A : Algorithm n w m),
        thermalError A ((length n:ℝ)⁻¹) 3 β D ≤ min 2
          (4*m*Real.sqrt (footprintSize n * Real.exp (-β*(3-kappa n ((length n:ℝ)⁻¹))))) ∧
        (∀ ε : ℝ, 0 < ε → β*(3-kappa n ((length n:ℝ)⁻¹)) ≥
          Real.log (footprintSize n) + 2*Real.log (4*m/ε) →
            thermalError A ((length n:ℝ)⁻¹) 3 β D ≤ ε)) ∧
      (∀ (E : StaticErrors n), branchWeight E ≤ (footprintSize n+3*n+3)*errorIncidence E ∧
        ∀ (D : Database n) (m w : ℕ), 1 ≤ m → ∀ A : Algorithm n w m,
          staticError A E ((length n:ℝ)⁻¹) 3 D ≤
            min 2 (2*m*(m+1)*(Real.pi*length n)*branchWeight E) ∧
          staticError A E ((length n:ℝ)⁻¹) 3 D ≤ C*m^2*errorIncidence E*(Real.log ((2:ℝ)^n))^4 ∧
          (∀ ε : ℝ, 0 < ε → errorIncidence E ≤ c*ε/(m^2*(Real.log ((2:ℝ)^n))^4) →
            staticError A E ((length n:ℝ)⁻¹) 3 D ≤ ε) ∧
          (∀ (d : ℕ) (δ ε : ℝ), 1 ≤ d → 0 < ε →
            (∀ q : ExtendedQubit n, (Finset.univ.filter fun α => q ∈ E.support α).card ≤ d) →
            (∀ α, E.bound α ≤ δ) → δ ≤ c*ε/(m^2*d*(Real.log ((2:ℝ)^n))^4) →
              staticError A E ((length n:ℝ)⁻¹) 3 D ≤ ε))) ∧
    (∀ (n : ℕ), 2 ≤ n → ∀ (m w : ℕ), 1 ≤ m → ∀ (β ε : ℝ), 0 < ε → ε < 1 →
      β ≥ C*(Real.log (Real.log ((2:ℝ)^n))+Real.log (m/ε)) →
        ∀ (D : Database n) (A : Algorithm n w m),
          thermalError A ((length n:ℝ)⁻¹) 3 β D ≤ ε) ∧
    (∀ (A a b g₀ : ℝ), 0 ≤ A → 0 ≤ a → 0 ≤ b → 0 < g₀ →
      ∃ cT : ℝ, 0 < cT ∧ ∀ (n : ℕ), 2 ≤ n → ∀ (m w : ℕ), 1 ≤ m →
        ∀ (ε T Ω Δ : ℝ), 0 < ε → ε < 1 → 0 < T → 0 < Ω →
          (m:ℝ) ≤ A*(n:ℝ)^a → ε⁻¹ ≤ A*(n:ℝ)^b → g₀ ≤ Δ-kappa n Ω →
          T ≤ cT/Real.log n → ∀ (D : Database n) (alg : Algorithm n w m),
            thermalError alg Ω Δ (T⁻¹) D ≤ ε) := by sorry

end ScalablePassiveQRAM.Device
