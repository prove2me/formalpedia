-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P29_canonical_heralded_perfect
-- name    : QAlgorithms.Papers.Independent.Next46.P29.canonical_heralded_perfect
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:19:28.947522+00:00
-- url     : https://prove2.me/theorems/517abf68-a318-4364-92aa-059772ced8db
-- title:
--   Good-sector postselection achieves perfect recovery
-- statement:
--   For a compact Lie group with normalized Haar measure, use the paired canonical token, an irreducible positive-dimensional message representation, and an exhaustive based decomposition of their actual tensor representation. A sector $q$ is good when its reciprocal-coupling projection is the identity. Define the accepted operation by projecting onto each good joint sector, tracing its carrier, and applying the constructed extraction $\mathcal R_q$. This operation is completely positive and trace-nonincreasing, and for every message density operator,
--
--   $$\mathcal R_{\mathrm{ok}}\mathcal E(\rho)=p_{\mathrm{perfect}}\rho,\qquad p_{\mathrm{perfect}}=\frac{1}{D_R}\sum_{q\ \mathrm{good}}d_q^2\in[0,1].$$
--
--   The accepted trace is exactly this probability. An empty good set gives zero success. This is an achieved construction, not an optimality claim.
-- source:
--   Quantum communication using a bounded-size quantum reference frame, arXiv:0812.5040v2, PDF p. 10, §III.D: heralded perfect decoding, Eq.(47)

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

/-- PDF p.10, Eq.(47): accepting good reciprocal sectors is a physical
heralded operation with the stated input-independent success probability.
An empty set of good sectors gives the zero subchannel and zero success. -/
theorem canonical_heralded_perfect (hLie : HasLieStructure G)
    (C : CanonicalToken G) {s : ℕ} (hs : 0 < s) (U : BasedUnitaryRep G s)
    (hIrrep : IsIrreducible (asProjectiveRep U)) (J : JointDecomposition C U) :
    IsSubchannel (relationalAccepted mu J) ∧
    0 ≤ relationalSuccess mu J ∧ relationalSuccess mu J ≤ 1 ∧
    ∀ rho, IsDensityMatrix rho →
      relationalAccepted mu J (canonicalEncoding mu C U rho) =
        (relationalSuccess mu J : ℂ) • rho ∧
      (relationalAccepted mu J (canonicalEncoding mu C U rho)).trace.re =
        relationalSuccess mu J := by sorry

end GeneralResults

end QAlgorithms.Papers.Independent.Next46.P29

end
