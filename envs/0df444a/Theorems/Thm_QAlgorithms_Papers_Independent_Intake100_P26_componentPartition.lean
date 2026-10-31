-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P26_componentPartition
-- name    : QAlgorithms.Papers.Independent.Intake100.P26.componentPartition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:23:42.627655+00:00
-- url     : https://prove2.me/theorems/3bea1e42-7aa5-4b9e-835d-6bf9bac2a227
-- title:
--   The complete calibration-component partition
-- statement:
--   Let $R$ be a finite reduced irreducible crystallographic root system of positive rank, with a fixed positive system and simple roots $\alpha_i$, Weyl group $W$, and full weight lattice $P$. Fix $q\in\mathbb C^\times$ which is not a root of unity. Write $\widetilde H$ for its affine Hecke algebra with $T_i^2=(q-q^{-1})T_i+1$ and the Bernstein relation with denominator $1-X^{-\alpha_i}$ interpreted as a Laurent-polynomial divided difference. Let $T=\operatorname{Hom}(P,\mathbb C^\times)$, with $(wt)(X^\lambda)=t(X^{w^{-1}\lambda})$. All modules below are finite dimensional complex left modules. Irreducible modules are nonzero.
--
--   For $t\in T$ define $Z(t)=\{\alpha>0:t(X^\alpha)=1\}$ and $P_q(t)=\{\alpha>0:t(X^\alpha)=q^{\pm2}\}$. For $J\subseteq P_q(t)$ put $F(t,J)=\{w:R(w)\cap Z(t)=\varnothing,\ R(w)\cap P_q(t)=J\}$, with $R(w)=\{\alpha>0:w\alpha<0\}$. Let $\Gamma(t)$ have vertices $Wt$ and distinct-endpoint calibration edges as above. For every vertex $b\in Wt$ there is a unique $J\subseteq P_q(t)$ with $F(t,J)\ne\varnothing$ such that
--   $$\{c:c\sim_{\Gamma(t)}b\}=\{wt:w\in F(t,J)\}.$$
--   Thus these images in the orbit, rather than the sets of Weyl elements themselves, form exactly the connected-component partition. The statement includes coverage, connectedness, and uniqueness of the label.
-- source:
--   Calibrated representations of affine Hecke algebras, arXiv:math/0401323v2, PDF p. 10, Theorem 2.14

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P26

open scoped BigOperators

variable {D : Datum} {V U : Type*}

variable [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]

/-- Theorem 2.14, PDF pp.10--11: complete, unique component labels, with
components the IMAGES of tableaux in the orbit. This includes coverage,
connectedness and disjointness, rather than only edge containment. -/
theorem componentPartition (D : Datum) (q : ℂ) (hq : GoodParameter q) (t : Torus D) :
    ∀ u ∈ characterOrbit D t, ∃! J : Set (Fin D.rootCount),
      PlacedShape D q t J ∧
      ∀ v : Torus D, Connected D q u v ↔ v ∈ tableauWeights D q t J := by sorry

end QAlgorithms.Papers.Independent.Intake100.P26

end
