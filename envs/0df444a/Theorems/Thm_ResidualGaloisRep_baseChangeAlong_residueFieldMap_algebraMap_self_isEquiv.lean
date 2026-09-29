-- Prove2me | Theorems.Thm_ResidualGaloisRep_baseChangeAlong_residueFieldMap_algebraMap_self_isEquiv
-- name    : ResidualGaloisRep.baseChangeAlong_residueFieldMap_algebraMap_self_isEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/95f66ece-f86d-53c9-981f-b4e0363bb867
-- title:
--   Base change along the identity residue-field map
-- statement:
--   Let $\mathcal{O}$ be a commutative local ring and let $k = \mathrm{IsLocalRing.ResidueField}\,\mathcal{O}$ be its residue field. Let $\rho$ be a residual Galois representation over $k$ in the sense of the project: a $k$-vector space $V$ with $\dim_k V = 2$, together with a monoid homomorphism from the group $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ` to $\mathrm{End}_k(V)$ which factors through a finite level, i.e. there is an intermediate field $L$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, such that every $\sigma$ fixing $L$ pointwise is sent to $1$. Consider the ring homomorphism $k \to k$ induced on residue fields by the structure map $\mathrm{algebraMap}\ \mathcal{O}\ \mathcal{O}$, and the base change of $\rho$ along it: the representation with underlying space $k \otimes_k V$, where $\sigma$ acts by the base change of $\rho(\sigma)$, $k$ being viewed as a $k$-algebra via that homomorphism. The assertion is that this base change is equivalent to $\rho$, that is, there exists a $k$-linear isomorphism $k \otimes_k V \to V$ commuting with the action of every $\sigma$ on both sides.
--
--   A bookkeeping compatibility: base change of a residual representation along the residue-field map induced by the identity of $\mathcal{O}$ changes nothing up to equivalence. It is used, in this orientation (base change on the left), to match the residual-comparison hypothesis in the modularity-lifting statements at conductor $3\cdot 5$ for Frey curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_baseChangeAlong_residueFieldMap_algebraMap_self_isEquiv.lean

import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Definitions.Def_GaloisRep_ResidualEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ResidualGaloisRep.baseChangeAlong_residueFieldMap_algebraMap_self_isEquiv {𝒪 : Type}
    [CommRing 𝒪] [IsLocalRing 𝒪] (ρ : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)) :
    (ρ.baseChangeAlong (IsLocalRing.ResidueField.map (algebraMap 𝒪 𝒪))).IsEquiv ρ := by sorry
