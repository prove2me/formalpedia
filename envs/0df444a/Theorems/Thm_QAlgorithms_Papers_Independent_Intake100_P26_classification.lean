-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P26_classification
-- name    : QAlgorithms.Papers.Independent.Intake100.P26.classification
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:27:33.882375+00:00
-- url     : https://prove2.me/theorems/b12d5309-83d8-4d97-80cc-442b34fead3b
-- title:
--   Exhaustive classification by the unique component model
-- statement:
--   Let $R$ be a finite reduced irreducible crystallographic root system of positive rank, with a fixed positive system and simple roots $\alpha_i$, Weyl group $W$, and full weight lattice $P$. Fix $q\in\mathbb C^\times$ which is not a root of unity. Write $\widetilde H$ for its affine Hecke algebra with $T_i^2=(q-q^{-1})T_i+1$ and the Bernstein relation with denominator $1-X^{-\alpha_i}$ interpreted as a Laurent-polynomial divided difference. Let $T=\operatorname{Hom}(P,\mathbb C^\times)$, with $(wt)(X^\lambda)=t(X^{w^{-1}\lambda})$. All modules below are finite dimensional complex left modules. Irreducible modules are nonzero.
--
--   Let $M$ be irreducible and calibrated, and fix $t\in T$ representing its central character $Wt$. Put $Z(t)=\{\alpha>0:t(X^\alpha)=1\}$, $P_q(t)=\{\alpha>0:t(X^\alpha)=q^{\pm2}\}$ and $R(w)=\{\alpha>0:w\alpha<0\}$. There is a unique subset $J\subseteq P_q(t)$ such that $(t,J)$ is a placed skew shape and
--   $$M\cong\widetilde H^{(t,J)}.$$
--   The module on the right is the explicit basis model of Theorem 3.1. For every canonical representative $w$ with $R(w)\cap Z(t)=\varnothing$ and $M_{wt}\ne0$, this label is $J=R(w)\cap P_q(t)$ and
--   $$\operatorname{supp}(M)=\{ut:u\in F(t,J)\},\qquad F(t,J)=\{u:R(u)\cap Z(t)=\varnothing,\ R(u)\cap P_q(t)=J\}.$$
--   Thus support is exactly one calibration component and its component model determines the module. Restricting the printed arbitrary representative to canonical representatives repairs the stabilizer ambiguity; uniqueness is asserted only after fixing $t$.
-- source:
--   Calibrated representations of affine Hecke algebras, arXiv:math/0401323v2, PDF p. 18, Theorem 4.5

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P26

open scoped BigOperators

variable {D : Datum} {V U : Type*}

variable [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]

/-- Theorem 4.5, PDF p.18. A fixed central-character representative has a
unique component label. The printed 'any w' is corrected to canonical
representatives R(w) intersect Z(t) = empty, as used in Theorem 2.14 and the
proof. Raw pairs with different base characters are not asserted distinct. -/
theorem classification (D : Datum) (q : ℂ) (hq : GoodParameter q)
    (A : HeckeGenerators D V) [FiniteDimensional ℂ V] (hA : Relations q A)
    (hirr : HeckeIrreducible A) (hcal : Calibrated A) (t : Torus D)
    (hcentral : CentralCharacter A t) :
    (∃! J : Set (Fin D.rootCount),
      PlacedSkewShape D q t J ∧ HeckeEquivalent A (tableauGenerators D q t J)) ∧
    (∀ w : Weyl D, inversions D w ∩ zeroRoots D t = ∅ →
      weightSpace A (weylCharacter D w t) ≠ ⊥ →
      let J := inversions D w ∩ poleRoots D q t
      PlacedSkewShape D q t J ∧ HeckeEquivalent A (tableauGenerators D q t J) ∧
        generalizedSupport A = tableauWeights D q t J) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P26

end
