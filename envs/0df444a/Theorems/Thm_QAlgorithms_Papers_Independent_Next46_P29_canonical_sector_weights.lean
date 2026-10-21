-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P29_canonical_sector_weights
-- name    : QAlgorithms.Papers.Independent.Next46.P29.canonical_sector_weights
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:17:27.732329+00:00
-- url     : https://prove2.me/theorems/dff9add0-e0da-459e-b2b4-62801e988d32
-- title:
--   Irreducible messages have input-independent sector weights
-- statement:
--   Let the compact-group Haar encoding use the paired canonical token on the restricted space of dimension $D_R>0$. Assume the message representation is irreducible of dimension $d_S>0$, and fix an exhaustive based isotypic decomposition of the actual joint representation. In sector $q$, let $d_q>0$ be the carrier dimension, $m_q>0$ the multiplicity dimension, and $\mathcal E_q(\rho)$ the carrier partial trace of the encoded block. Then for every message density operator,
--
--   $$\operatorname{Tr}\mathcal E_q(\rho)=p_q=\frac{d_qm_q}{D_Rd_S}.$$
--
--   Thus the sector probability depends only on dimensions. No such independence is asserted for a general reducible message representation.
-- source:
--   Quantum communication using a bounded-size quantum reference frame, arXiv:0812.5040v2, PDF p. 7, §II.B: input-independent sector weights, Eq.(34)

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

/-- PDF pp.7–8, Eq.(34): for an irreducible message, every isotypic sector has
input-independent probability equal to its dimension divided by `D_R d_S`.
The decomposition is of the actual tensor representation, not an assumed channel. -/
theorem canonical_sector_weights (hLie : HasLieStructure G)
    (C : CanonicalToken G) {s : ℕ} (hs : 0 < s) (U : BasedUnitaryRep G s)
    (hIrrep : IsIrreducible (asProjectiveRep U)) (J : JointDecomposition C U) :
    ∀ rho, IsDensityMatrix rho → ∀ q : Fin J.count,
      (sectorBlock J q (canonicalEncoding mu C U rho)).trace =
        ((J.dim q * J.mult q : ℕ) : ℂ) / ((tokenDimension C : ℂ) * (s : ℂ)) := by sorry

end GeneralResults

end QAlgorithms.Papers.Independent.Next46.P29

end
