-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P29_canonical_two_decoders
-- name    : QAlgorithms.Papers.Independent.Next46.P29.canonical_two_decoders
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:18:54.08337+00:00
-- url     : https://prove2.me/theorems/6e5d1342-9bc6-45b7-b237-27f6da4a8d03
-- title:
--   Covariant measurement and relational extraction implement the same recovery
-- statement:
--   Use the paired canonical token for a compact Lie group with normalized Haar measure and an irreducible positive-dimensional message. In an actual exhaustive based joint decomposition, let $B_q$ be the isotypic inclusions, $A_q$ the contraction isometries, $P_q=A_qA_q^\dagger$ their reciprocal-coupling projections, $\mathcal E_q$ the directly constructed encoding blocks, and $\mathcal R_q(Z)=\operatorname{Tr}_{M_q^*}(A_qZA_q^\dagger)$. For every joint operator $Y$,
--
--   $$\mathcal R(Y)=D_R\int K_g^\dagger YK_g dg=\sum_q\mathcal R_q\bigl(\operatorname{Tr}_{M_q}(B_q^\dagger YB_q)\bigr),\qquad\mathcal R_q=\frac{D_R}{d_q}\mathcal E_q^\dagger.$$
--
--   Each $\mathcal R_q$ is a quantum channel. For every message density operator,
--
--   $$\mathcal R\mathcal E(\rho)=\sum_q\frac{d_q}{D_R}\operatorname{Tr}_{M_q^*}\bigl[P_q(I_{M_q^*}\otimes\rho)P_q\bigr].$$
--
--   These are exact measurement/reorientation and relational-extraction implementations of one recovery. The factor in the block adjoint identity follows Eq.(42).
-- source:
--   Quantum communication using a bounded-size quantum reference frame, arXiv:0812.5040v2, PDF p. 8, §III.A–C: two implementations of the same recovery, Eqs.(39), (41)–(46)

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

/-- PDF pp.8–10, Eqs.(39),(41)–(46): two exact implementations of the same
recovery on every joint operator, together with the projector formula for its
composition with encoding. Eq.(42) fixes the correct factor `D_R/d_q` multiplying
the block adjoint; the printed `d_q` after Eq.(42) and in Eq.(43) is inconsistent. -/
theorem canonical_two_decoders (hLie : HasLieStructure G)
    (C : CanonicalToken G) {s : ℕ} (hs : 0 < s) (U : BasedUnitaryRep G s)
    (hIrrep : IsIrreducible (asProjectiveRep U)) (J : JointDecomposition C U) :
    (∀ Y, canonicalRecovery mu C U Y =
      ∑ q, relationalRecovery J q (sectorBlock J q Y)) ∧
    (∀ q, IsChannel (relationalRecovery J q) ∧
      ∀ X Z, (Xᴴ * relationalRecovery J q Z).trace =
        ((tokenDimension C : ℂ) / J.dim q) * ((relationalEncoding J q X)ᴴ * Z).trace) ∧
    (∀ rho, IsDensityMatrix rho →
      canonicalRecovery mu C U (canonicalEncoding mu C U rho) =
        ∑ q, ((J.dim q : ℂ) / tokenDimension C) •
          traceLeft (reciprocalProjector mu J q *
            ((1 : Matrix (Fin (J.dim q)) (Fin (J.dim q)) ℂ).kronecker rho) *
              reciprocalProjector mu J q)) := by sorry

end GeneralResults

end QAlgorithms.Papers.Independent.Next46.P29

end
