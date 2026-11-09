-- Prove2me | Theorems.Thm_ScalablePassiveQRAM_Device_noise_resilience_guarantee
-- name    : ScalablePassiveQRAM.Device.noise_resilience_guarantee
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:56:16.984053+00:00
-- url     : https://prove2.me/theorems/6cb97e89-271d-4213-bac0-8d767e923b80
-- title:
--   Theorem 2 — Noise resilience guarantee
-- statement:
--   For the explicit witness $\Omega=1/L,\Delta=3$, there are uniform constants $C,c>0$. For $n\ge2$, $m\ge1$, and $0<\varepsilon<1$, the thermal channel with the device discarded has error at most $\varepsilon$ once
--
--   $$\beta\ge C(\log\log N+\log(m/\varepsilon)).$$
--
--   In the separate clean static preparation and recorded interface, for $n\ge1$ and $\varepsilon>0$, error is at most $\varepsilon$ when
--
--   $$\lambda_{\rm err}\le\frac{c\varepsilon}{m^2\log^4N}.$$
--
--   Both statements quantify over every database, finite workspace, and inter-query algorithm. Taking $m=1$ recovers both one-query clauses, and polynomially small $\varepsilon$ gives the source's inverse-logarithmic thermal temperature scaling. This combines the two noise guarantees without claiming they hold under a joint preparation.
--
--   Differences from the source:
--   - encoding: one-based bit and transition indices and tensor-product register notation → zero-based finite index types and matrices on all physical bit configurations; reason: the finite types enumerate the same modes and every operation is lifted to the full tensor product
--   - reading: unload reverses the load and routing uses the values that can occur on a valid history → unload bits in decreasing order and explicit bit or star flavor sets at every route; reason: the source leaves this schedule implicit; this is the execution described in §§3.1–3.2 and reproduces the layer counts
--   - encoding: rectangular unhalved diamond norm of the explicitly constructed channels → the identical density-operator supremum over every finite reference dimension for explicit superoperators, using the published trace norm; reason: this avoids inserting substantive CPTP proofs into definitions; the physical maps are encoding, unitary evolution, partial trace, replacement, and decoding channels
--   - encoding: there exists a scalable device family with Ω=Θ(1/L) and fixed on-site gap → the explicit witness Ω=1/L, Δ=3; reason: the source gives an existence claim; this witness has J_*≤1/2, κ≤10/9 and g≥1
--   - encoding: asymptotic log log N bounds → n≥2 for log log N formulas, with exact bounds also stated for n=1; reason: log log 2 is negative; these are asymptotic statements and the finite-size guarantees are kept without narrowing
--   - reading: Theorem 2(ii) names E_D while the schematic equation (4) keeps memory D unchanged → the §4.3 induced channel with the recorded interface and memory traced out, targeting original D; reason: §1.2 says (ii) is proved in §4.3, whose perturbations may flip memory and whose root record is explicit
-- source:
--   Siddhartha Jain, Alexander Dalzell, Connor Hann, STOC 2027 submission #129 (October 2026), Theorem 2, p. 7–8. Canonical PDF SHA256 725dff5ab83fbe7e163da05440b75cc1d24f83804408cc139eb8954d2f8a076e.

import Definitions.Def_ScalablePassiveQRAM_Device_Energy
import Mathlib

open scoped BigOperators Matrix
set_option synthInstance.maxSize 10000
noncomputable section

namespace ScalablePassiveQRAM.Device
local instance noise_resilience_guaranteeDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance noise_resilience_guaranteeDecidableEq (a : Type) : DecidableEq a := Classical.decEq a

theorem noise_resilience_guarantee :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    (∀ (n : ℕ), 2 ≤ n → ∀ (m w : ℕ), 1 ≤ m → ∀ (β ε : ℝ), 0 < ε → ε < 1 →
      β ≥ C*(Real.log (Real.log ((2:ℝ)^n))+Real.log (m/ε)) →
      ∀ (D : Database n) (A : Algorithm n w m),
        diamondDist (fun X => WildeQIT.partialTraceRight (thermalAlgorithm A ((length n:ℝ)⁻¹) 3 β D X))
          (idealAlgorithm A D) ≤ ε) ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ (m w : ℕ), 1 ≤ m → ∀ (ε : ℝ), 0 < ε →
      ∀ (D : Database n) (E : StaticErrors n) (A : Algorithm n w m),
        errorIncidence E ≤ c*ε/(m^2*(Real.log ((2:ℝ)^n))^4) →
          staticError A E ((length n:ℝ)⁻¹) 3 D ≤ ε) := by sorry

end ScalablePassiveQRAM.Device
