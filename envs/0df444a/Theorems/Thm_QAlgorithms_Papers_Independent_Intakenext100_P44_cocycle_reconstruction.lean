-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P44_cocycle_reconstruction
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P44.cocycle_reconstruction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:51:48.155235+00:00
-- url     : https://prove2.me/theorems/2b26c055-f407-4866-912d-556494d5b6d7
-- title:
--   Cocycle reconstruction and its canonical equivalence
-- statement:
--   Let $M$ be a topological space, $K$ a topological group, and $(U_i)_{i\in I}$ an open cover of $M$. Suppose that the continuous transition maps $k_{ij}:U_i\cap U_j\to K$ satisfy $k_{ii}=1$ and $k_{ij}k_{jn}k_{ni}=1$ on triple intersections. Give the disjoint union of the products $U_i\times K$ its sum topology, and form the quotient
--
--   $$
--   P_k=\left(\coprod_{i\in I}U_i\times K\right)/\sim,
--   \qquad (i,x,a)\sim(j,x,b)\ \Longleftrightarrow\ b=k_{ji}(x)a.
--   $$
--
--   With its quotient topology, projection $[i,x,a]\mapsto x$, and right action $[i,x,a]\cdot b=[i,x,ab]$, this is a continuous principal $K$-bundle. Its local inverse trivializations are $(x,a)\mapsto[i,x,a]$.
--
--   If a continuous principal bundle $P$ has trivializations $\Omega_i$ giving these transition maps by $\Omega_i^{-1}(x,1)\cdot k_{ij}(x)=\Omega_j^{-1}(x,1)$, then
--
--   $$
--   \Omega(p)=[i,\Omega_i(p)],\qquad
--   \Omega^{-1}([i,x,a])=\Omega_i^{-1}(x,a)
--   $$
--
--   are well defined and define an equivariant homeomorphism over the identity on $M$. The first formula holds for every chart containing the base point of $p$.
--
--   This reconstructs the geometric bundle from transition data and recovers any bundle from its local trivializations.
-- source:
--   Equivalences of Smooth and Continuous Principal Bundles with Infinite-Dimensional Structure Group, arXiv:math/0604142v3, PDF p. 3, Remark I.2: cocycle reconstruction and canonical bundle equivalence

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P44

open Set

open scoped ContDiff

/-- Remark I.2, PDF p. 3: a continuous cocycle reconstructs a principal bundle
with the stated quotient, action and charts. When the cocycle comes from a given
bundle by equation (1), the specified canonical map is an equivariant homeomorphism
over the identity, with the stated inverse on every representative. -/
theorem cocycle_reconstruction
    {M K I : Type*} [TopologicalSpace M] [TopologicalSpace K] [Group K]
    [IsTopologicalGroup K] {u : I → Set M} (c : ContinuousCocycle (K := K) u) :
    (∃ a : PrincipalAtlas (cocycleProjection c) (cocycleRightAction c) u,
      ∀ i (x : u i) k,
        ((a.trivialization i).symm (x, k)).val =
          Quot.mk (CocycleRelation c) ⟨i, x, k⟩) ∧
    (∀ {P : Type*} [TopologicalSpace P] (eta : P → M) (act : P → K → P)
      (a : PrincipalAtlas eta act u),
      (∀ i j (x : M) (hi : x ∈ u i) (hj : x ∈ u j),
        act ((a.trivialization i).symm (⟨x, hi⟩, 1)).val
          (c.transition i j ⟨x, hi, hj⟩) =
          ((a.trivialization j).symm (⟨x, hj⟩, 1)).val) →
      ∃ e : P ≃ₜ CocycleTotal c,
        (∀ p, e p = canonicalBundleMap c a p) ∧
        (∀ i (p : P) (hp : eta p ∈ u i),
          e p = Quot.mk (CocycleRelation c) ⟨i, a.trivialization i ⟨p, hp⟩⟩) ∧
        (∀ i (x : u i) k,
          e.symm (Quot.mk (CocycleRelation c) ⟨i, x, k⟩) =
            ((a.trivialization i).symm (x, k)).val) ∧
        (∀ p, cocycleProjection c (e p) = eta p) ∧
        (∀ p k, e (act p k) = cocycleRightAction c (e p) k)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P44

end
