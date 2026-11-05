-- Prove2me | Theorems.Thm_RepGQML_intertwiner_eq_tensor_id
-- name    : RepGQML.intertwiner_eq_tensor_id
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:43:30.968009+00:00
-- url     : https://prove2.me/theorems/5aa157a2-87a7-4b28-ab4d-04687e17bd68
-- title:
--   p.29 — intertwiners of multiples of one irrep are exactly $B\otimes\mathbb 1$
-- statement:
--   Let $\rho$ be an irreducible complex representation of a group $G$ on a finite dimensional $V$. A linear map $T:\mathbb C^{m}\otimes V\to\mathbb C^{m'}\otimes V$ satisfies
--   $$
--   T\circ(\mathbb 1_{m}\otimes\rho_g)=(\mathbb 1_{m'}\otimes\rho_g)\circ T\qquad\text{for all }g\in G
--   $$
--   if and only if $T=B\otimes\mathbb 1_{V}$ for a linear map $B:\mathbb C^{m}\to\mathbb C^{m'}$.
--
--   This is the precise meaning of the sentence that elements of the commutant act only among multiplicities, and it gives the blocks of the display (30).
--
--   Differences from the source:
--   - reading: "the elements of the commutant can really only act upon irreps among multiplicities" → an intertwiner of 𝟙_m ⊗ ρ and 𝟙_m' ⊗ ρ is B ⊗ 𝟙, and conversely; reason: the sentence is informal; this is its precise form for one block of (30)
--   - generalization: B_{m_k} an operator on one m_k-dimensional space; a unitary representation of a compact group → B : ℂ^m → ℂ^m' with m, m' allowed to differ; ρ any irreducible finite dimensional complex representation of any group; reason: m = m' with ρ unitary is the source case
--   - encoding: irreducible (Def 13, read literally, also admits V = 0) → Representation.IsIrreducible, which requires a nonzero space; reason: Mathlib convention; a zero summand adds nothing, and V = 0 has the empty decomposition
-- source:
--   Ragone et al., Representation Theory for Geometric Quantum Machine Learning, arXiv:2210.07980v2, p.29, the paragraph after (32)

import Mathlib

namespace RepGQML

open scoped TensorProduct in
/-- Intertwiners between multiples of one irrep act only on the multiplicities (Ragone et al., *Representation Theory for Geometric Quantum Machine Learning*, arXiv:2210.07980v2, p.29,
"the elements of the commutant can really only act upon irreps among multiplicities"): for `ρ`
irreducible on a finite dimensional `V`, a map `T : ℂ^m ⊗ V → ℂ^{m'} ⊗ V` intertwines `𝟙 ⊗ ρ_g` if
and only if `T = B ⊗ 𝟙` for a linear `B : ℂ^m → ℂ^{m'}`.

**Formalization Note** The sentence on the page is informal. This is its precise form, with `m` and
`m'` allowed to differ; `m = m'` is the case used in Theorem 7. -/
theorem intertwiner_eq_tensor_id {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (hρ : ρ.IsIrreducible) (m m' : ℕ)
    (T : EuclideanSpace ℂ (Fin m) ⊗[ℂ] V →ₗ[ℂ] EuclideanSpace ℂ (Fin m') ⊗[ℂ] V) :
    (∀ g : G, T ∘ₗ TensorProduct.map LinearMap.id (ρ g) =
        TensorProduct.map LinearMap.id (ρ g) ∘ₗ T) ↔
      ∃ B : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m'),
        T = TensorProduct.map B LinearMap.id := by sorry

end RepGQML
