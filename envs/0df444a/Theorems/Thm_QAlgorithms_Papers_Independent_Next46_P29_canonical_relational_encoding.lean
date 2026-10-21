-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P29_canonical_relational_encoding
-- name    : QAlgorithms.Papers.Independent.Next46.P29.canonical_relational_encoding
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:16:47.37571+00:00
-- url     : https://prove2.me/theorems/81c5f1a9-55cd-4526-8bb9-323214604422
-- title:
--   Relational encoding and its exact reciprocal-coupling range
-- statement:
--   For the paired canonical token of a compact Lie group with normalized Haar measure, assume that the positive-dimensional message representation $U_S$ is irreducible. Fix an exhaustive orthogonal based decomposition of the actual joint representation, with inequivalent carrier representations $U_q$ of dimensions $d_q$, multiplicity spaces $N_q$ of dimensions $m_q>0$, and isometric inclusions $B_q:M_q\otimes N_q\to\bar H_R\otimes H_S$. Define $\mathcal E_q(\rho)=\operatorname{Tr}_{M_q}[B_q^\dagger(|e\rangle\langle e|\otimes\rho)B_q]$. Define $A_q:N_q\to M_q^*\otimes H_S$ by the based contraction $(A_q)_{(\mu,b),a}=\sqrt{D_R/d_q}\sum_r(B_q)_{(r,b),(\mu,a)}\overline{e_r}$. Let $P_q$ be the isotypic projection in $M_q^*\otimes H_S$ onto all conjugate token irreps retained in $\bar H_R$. Then
--
--   $$\mathcal E(\rho)=\sum_qB_q\bigl((I_{M_q}/d_q)\otimes\mathcal E_q(\rho)\bigr)B_q^\dagger,\quad A_q^\dagger A_q=I_{N_q},\quad A_qA_q^\dagger=P_q,\quad\mathcal E_q(\rho)=\frac{d_q}{D_R}A_q^\dagger(I_{M_q^*}\otimes\rho)A_q.$$
--
--   The range of $A_q$ is exactly the fixed space of $P_q$, and $A_q$ is surjective exactly when $P_q=I$. It intertwines the induced right action on $N_q$ with $\overline{U_q}\otimes U_S$. In a good sector $P_q=I$, extraction $\mathcal R_q(Z)=\operatorname{Tr}_{M_q^*}(A_qZA_q^\dagger)$ recovers $(d_q^2/D_R)\rho$. In a bad sector, no trace-preserving completely positive decoder recovers $p_q\rho$ for every density operator, where $p_q=d_qm_q/(D_Rd_S)$. This identifies the physical, rather than merely linear, reversibility of each branch.
-- source:
--   Quantum communication using a bounded-size quantum reference frame, arXiv:0812.5040v2, PDF p. 6, §II.B Main result: relational-subsystem encoding, Eqs.(22)–(33)

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

/-- PDF pp.6–8, Eqs.(22)–(33),(37): full relational block formula, canonical
isometry and its precise reciprocal-coupling range. Incomplete reciprocal sectors
have no deterministic physical inverse; this does not claim linear noninjectivity. -/
theorem canonical_relational_encoding (hLie : HasLieStructure G)
    (C : CanonicalToken G) {s : ℕ} (hs : 0 < s) (U : BasedUnitaryRep G s)
    (hIrrep : IsIrreducible (asProjectiveRep U)) (J : JointDecomposition C U) :
    (∀ rho, IsDensityMatrix rho → canonicalEncoding mu C U rho =
      ∑ q, J.basis q *
        (((J.dim q : ℂ)⁻¹ • (1 : Matrix (Fin (J.dim q)) (Fin (J.dim q)) ℂ)).kronecker
          (relationalEncoding J q rho)) * (J.basis q)ᴴ) ∧
    (∀ q,
      (relationalIsometry J q)ᴴ * relationalIsometry J q = 1 ∧
      relationalIsometry J q * (relationalIsometry J q)ᴴ = reciprocalProjector mu J q ∧
      Set.range (Matrix.mulVec (relationalIsometry J q)) =
        {v | Matrix.mulVec (reciprocalProjector mu J q) v = v} ∧
      (Function.Surjective (Matrix.mulVec (relationalIsometry J q)) ↔
        reciprocalProjector mu J q = 1) ∧
      (∀ h, relationalIsometry J q * sectorRight J q h =
        (Matrix.kronecker (Matrix.of fun a b => conj (repMatrix (J.rep q) h a b)) (repMatrix U h)) *
          relationalIsometry J q) ∧
      (∀ rho, IsDensityMatrix rho →
        sectorBlock J q (canonicalEncoding mu C U rho) = relationalEncoding J q rho ∧
        relationalEncoding J q rho = ((J.dim q : ℂ) / tokenDimension C) •
          ((relationalIsometry J q)ᴴ *
            ((1 : Matrix (Fin (J.dim q)) (Fin (J.dim q)) ℂ).kronecker rho) *
              relationalIsometry J q)) ∧
      (reciprocalProjector mu J q = 1 → ∀ rho, IsDensityMatrix rho →
        relationalRecovery J q (relationalEncoding J q rho) =
          ((J.dim q : ℂ) ^ 2 / tokenDimension C) • rho) ∧
      (reciprocalProjector mu J q ≠ 1 →
        ∀ D : Superop (Fin (J.mult q)) (Fin s), IsChannel D →
          ∃ rho, IsDensityMatrix rho ∧ D (relationalEncoding J q rho) ≠
            (((J.dim q * J.mult q : ℕ) : ℂ) /
              ((tokenDimension C : ℂ) * (s : ℂ))) • rho)) := by sorry

end GeneralResults

end QAlgorithms.Papers.Independent.Next46.P29

end
