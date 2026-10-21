-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P29_canonical_near_optimal_uniform
-- name    : QAlgorithms.Papers.Independent.Next46.P29.canonical_near_optimal_uniform
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:18:18.249997+00:00
-- url     : https://prove2.me/theorems/a29ced0b-8e88-4ed8-9fe9-329fbdc39021
-- title:
--   Twice-optimal entanglement infidelity for uniform input
-- statement:
--   Fix the paired canonical token, compact Lie group with normalized Haar measure, and positive-dimensional continuous unitary message representation. Let $\mathcal E$ be the resulting encoding and $\mathcal R=D_R\mathcal E^\dagger$ its fixed recovery. Write $F_e(I_S/d_S,\Phi)$ for the normalized entanglement fidelity obtained from a maximally entangled purification of the maximally mixed message. Every deterministic completely positive trace-preserving decoder $\mathcal D$ satisfies
--
--   $$1-F_e(I_S/d_S,\mathcal R\mathcal E)\le 2\bigl(1-F_e(I_S/d_S,\mathcal D\mathcal E)\bigr).$$
--
--   This is the source's no-prior-information specialization of approximate reversal. The token remains fixed, and an unrestricted arbitrary-ensemble assertion is not made.
-- source:
--   Quantum communication using a bounded-size quantum reference frame, arXiv:0812.5040v2, PDF p. 8, §III: near-optimal deterministic recovery with no input prior

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P29

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Manifold ContDiff Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Next46.P29

open QAlgorithms.Papers.Independent.Information100.P56 (IsIrreducible)

open QAlgorithms.Papers.Independent.Information100.P63 (mixed)

open QAlgorithms.Papers.Independent.Information100.P34 (dephasing)

open QAlgorithms.Papers.Independent.Information100.P71 (IsSubchannel)

attribute [local instance] Classical.decEq Classical.propDecidable

section GeneralResults

variable {G : Type*} [Group G] [TopologicalSpace G] [hTop : IsTopologicalGroup G]
  [hCompact : CompactSpace G] [hT2 : T2Space G] [MeasurableSpace G] [hBorel : BorelSpace G]
  (mu : Measure G) [hHaar : Measure.IsHaarMeasure mu] [hProb : IsProbabilityMeasure mu]

include hTop hCompact hT2 hBorel hHaar hProb

/-- PDF p.8, §III: for the maximally mixed input, the fixed adjoint recovery has
entanglement infidelity at most twice that of every deterministic recovery.
The incompatible unqualified arbitrary-ensemble claim is deferred separately. -/
theorem canonical_near_optimal_uniform (hLie : HasLieStructure G)
    (C : CanonicalToken G) {s : ℕ} (hs : 0 < s) (U : BasedUnitaryRep G s) :
    ∀ D : Superop (TokenIndex C × Fin s) (Fin s), IsChannel D →
      1 - QuditFidelity.entanglementFidelity s hs (canonicalRecovery mu C U ∘ canonicalEncoding mu C U) ≤
        2 * (1 - QuditFidelity.entanglementFidelity s hs (D ∘ canonicalEncoding mu C U)) := by sorry

end GeneralResults

end QAlgorithms.Papers.Independent.Next46.P29

end
