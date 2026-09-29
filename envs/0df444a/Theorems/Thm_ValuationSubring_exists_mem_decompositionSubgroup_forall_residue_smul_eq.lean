-- Prove2me | Theorems.Thm_ValuationSubring_exists_mem_decompositionSubgroup_forall_residue_smul_eq
-- name    : ValuationSubring.exists_mem_decompositionSubgroup_forall_residue_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/b995b210-f966-5f5f-bb0a-59fd775b03f7
-- title:
--   Decomposition group surjects onto residue automorphisms (Hilbert–Krull)
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra such that $L/K$ is Galois (in Mathlib's sense: normal and separable, with no finiteness assumption), and let $A$ be a valuation subring of $L$. Since $A$ is a local ring, it has a residue field $\kappa(A)$, and the residue map $A \to \kappa(A)$ is available. Let $\varphi$ be a ring automorphism of $\kappa(A)$ (an isomorphism $\kappa(A) \simeq \kappa(A)$ of rings, equivalently of additive and multiplicative structure) which is assumed to fix the residue of every element of $K$ that lands in $A$: for every $x \in K$ and every proof that $\mathrm{algebraMap}_{K,L}(x) \in A$, $\varphi$ sends the residue of that element of $A$ to itself. The conclusion is that $\varphi$ is induced by an element of the decomposition group: there exists a $K$-algebra automorphism $\sigma$ of $L$ lying in the decomposition subgroup $A.\mathrm{decompositionSubgroup}\ K$, i.e. in the stabiliser of $A$ inside $\mathrm{Gal}(L/K)$, such that for every $a \in A$ the residue of $\sigma \bullet a$ (the action of $\sigma$, viewed as an element of that stabiliser, on $A$) equals $\varphi$ applied to the residue of $a$.
--
--   This is the Hilbert–Krull theorem in the setting of general Krull valuations: the decomposition group of a valuation subring in a Galois extension maps onto the group of automorphisms of the residue field that fix the residues of the base field, with no hypothesis on residue characteristic or on separability of the residue extension. It is used in the project to produce elements of the inertia subgroup with prescribed restriction, and to analyse residue fields of valuation subrings fixed by the decomposition group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_mem_decompositionSubgroup_forall_residue_smul_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Pointwise

theorem ValuationSubring.exists_mem_decompositionSubgroup_forall_residue_smul_eq
    {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (A : ValuationSubring L)
    (φ : IsLocalRing.ResidueField A ≃+* IsLocalRing.ResidueField A)
    (hφ : ∀ (x : K) (hx : algebraMap K L x ∈ A),
      φ (IsLocalRing.residue A ⟨algebraMap K L x, hx⟩) = IsLocalRing.residue A ⟨algebraMap K L x, hx⟩) :
    ∃ σ : L ≃ₐ[K] L, ∃ hσ : σ ∈ A.decompositionSubgroup K,
      ∀ a : A, IsLocalRing.residue A ((⟨σ, hσ⟩ : A.decompositionSubgroup K) • a) = φ (IsLocalRing.residue A a) := by sorry
