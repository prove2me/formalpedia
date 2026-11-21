-- Prove2me | Theorems.Thm_RiemannMasullo_adeleRing_factors
-- name    : RiemannMasullo.adeleRing_factors
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:45:35.152817+00:00
-- url     : https://prove2.me/theorems/bf429655-e7e0-429b-b9e5-0e2c87906ab6
-- title:
--   Topological factors of the adele ring
-- statement:
--   The infinite adele ring is topologically ring-isomorphic to the real scalar extension, the finite factor has the restricted-product topology, and the diagonal maps evaluate to the local embeddings.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec1.lean#L161-L210

import Mathlib


open Filter Function NumberField IsDedekindDomain Topology
open scoped NNReal RestrictedProduct NumberField.AdeleRing IsDedekindDomain.FiniteAdeleRing TensorProduct
variable (F : Type*) [Field F] [NumberField F]
local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)

namespace RiemannMasullo

theorem adeleRing_factors :
    letI := moduleTopology ℝ (ℝ ⊗[ℚ] F)
    (∃ e : (ℝ ⊗[ℚ] F) ≃+* InfiniteAdeleRing F, Continuous e ∧ Continuous e.symm ∧
      ∀ x : F, e (1 ⊗ₜ[ℚ] x) = algebraMap F (InfiniteAdeleRing F) x) ∧
    IsHomeomorph (fun a : 𝔸ᶠ[𝓞 F, F] ↦
      (a : Πʳ v : Primes(F), [v.adicCompletion F, v.adicCompletionIntegers F])) ∧
    IsHomeomorph (fun a : 𝔸[F] ↦ (a.1, a.2) : 𝔸[F] → InfiniteAdeleRing F × 𝔸ᶠ[𝓞 F, F]) ∧
    ∀ x : F, (∀ w, (algebraMap F 𝔸[F] x).1 w = algebraMap F w.Completion x) ∧
      ∀ v : Primes(F), (algebraMap F 𝔸[F] x).2 v = algebraMap F (v.adicCompletion F) x := by sorry

end RiemannMasullo
