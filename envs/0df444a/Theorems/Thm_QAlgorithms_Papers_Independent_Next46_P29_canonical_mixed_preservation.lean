-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P29_canonical_mixed_preservation
-- name    : QAlgorithms.Papers.Independent.Next46.P29.canonical_mixed_preservation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:15:06.566527+00:00
-- url     : https://prove2.me/theorems/3bab89c1-453f-48bd-bdd0-1c62fa5b11dd
-- title:
--   Canonical encoding preserves the maximally mixed state
-- statement:
--   Let $G$ be a compact Lie group with normalized Haar measure, $U_S$ a continuous unitary representation on a positive-dimensional message space of dimension $d_S$, and $\mathcal E$ the Haar-correlated encoding using the paired canonical token of Eq.(17). Its restricted token dimension is $D_R=\sum_qd_q^2>0$, where the finite nonempty family consists of inequivalent irreducible representations of positive dimensions $d_q$. Then
--
--   $$\mathcal E(I_S/d_S)=(I_{\bar R}/D_R)\otimes(I_S/d_S).$$
--
--   This is the paper's dimension-adjusted notion of unitality for a trace-preserving map between different-dimensional spaces.
-- source:
--   Quantum communication using a bounded-size quantum reference frame, arXiv:0812.5040v2, PDF p. 5, §II.A: maximally mixed preservation, Eq.(21)

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

/-- PDF pp.5–6, Eq.(21): dimension-adjusted unitality means preservation of the
normalized maximally mixed state, not equality of unnormalized identities. -/
theorem canonical_mixed_preservation (hLie : HasLieStructure G)
    (C : CanonicalToken G) {s : ℕ} (hs : 0 < s) (U : BasedUnitaryRep G s) :
    canonicalEncoding mu C U (mixed (O := Fin s)) =
      ((tokenDimension C : ℂ)⁻¹ • (1 : Matrix (TokenIndex C) (TokenIndex C) ℂ)).kronecker
        (mixed (O := Fin s)) := by sorry

end GeneralResults

end QAlgorithms.Papers.Independent.Next46.P29

end
