-- Prove2me | Theorems.Thm_RepGQML_commutant_structure
-- name    : RepGQML.commutant_structure
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:46:34.471657+00:00
-- url     : https://prove2.me/theorems/55406a85-4c90-4507-af2b-0480100bf8cc
-- title:
--   Theorem 7 — commutant structure: $\mathcal C(U)=\bigoplus_k\mathcal B_{m_k}\otimes\mathbb 1_{\dim(U_k)}$
-- statement:
--   Let $U$ be a unitary representation of a group $G$ on a finite dimensional complex Hilbert space $H$. Then both of the following hold.
--
--   1. **Decomposition.** There are an integer $K$, multiplicities $m_k\ge 1$, pairwise inequivalent irreducible unitary representations $U_k$ of $G$ on $\mathbb C^{d_k}$, and a surjective linear isometry $\Phi:H\to\bigoplus_{k=1}^K\mathbb C^{m_k}\otimes\mathbb C^{d_k}$ under which
--   $$
--   U=\bigoplus_{k=1}^K\mathbb 1_{m_k}\otimes U_k .
--   $$
--   2. **The commutant.** For every decomposition $\Phi$ of $U$ into pairwise inequivalent irreducible unitary representations $\rho_k$ on finite dimensional spaces $V_k$, with multiplicities $m_k$, an operator $T$ on $H$ lies in the commutant $\mathcal C(U)$ if and only if there are linear operators $B_k$ on $\mathbb C^{m_k}$ with
--   $$
--   \Phi(Tx)_k=(B_k\otimes\mathbb 1_{\dim V_k})\,\Phi(x)_k\qquad\text{for all } x\in H\text{ and all } k,
--   $$
--   that is,
--   $$
--   \mathcal C(U)=\bigoplus_{k=1}^K\mathcal B_{m_k}\otimes\mathbb 1_{\dim(U_k)} .
--   $$
--
--   So an operator commuting with $U$ acts only on the multiplicity spaces and does not connect different irreps. Equivariant quantum neural networks and equivariant measurements lie in this commutant, which is why this block structure limits what a geometric quantum machine learning model can access.
--
--   **Formalization Note** On a finite dimensional space every linear operator is bounded, so the source's "bounded operators" adds no analytic condition. The field must be $\mathbb C$: for $SO(2)$ on $\mathbb R^2$ the representation is irreducible and its commutant is $\mathbb C$, not $\mathbb R$.
--
--   Differences from the source:
--   - reading: the irreps U_k are not said to be inequivalent → ρ_k, ρ_l are inequivalent for k ≠ l, in IsIrrepDecomposition; reason: it is the only meaning of "multiplicity" (p.21, "K distinct irreducible invariant subspaces" on p.30, footnote 20); without it (30) is false: G trivial, H = ℂ², K = 2, m₁ = m₂ = 1, U₁ = U₂ trivial gives C(U) = M₂(ℂ) against the diagonal matrices
--   - reading: the Hilbert space H → H finite dimensional; reason: §VII.C restricts to finite dimensional representations (p.27), and the displayed decomposition has finite K, m_k and dim U_k
--   - reading: the elements of its commutant are of the following form, with the equality (30) → T ∈ C(U) if and only if T has the form; reason: (30) is an equality, so both inclusions are meant
--   - generalization: a compact group → any group; reason: compactness is used in the source only to get unitarity (Theorem 5, p.27), which is assumed here; a compact group with continuous U is an instance
--   - generalization: the decomposition is given → clause 1 also asserts that a decomposition exists, with Φ an isometry and every m_k ≥ 1; reason: it is supplied by Theorem 4 and p.28, and it makes clause 2 non-vacuous for every U
--   - generalization: the identification of H with the direct sum is a change of basis between unitary representatives → clause 2 quantifies over Φ only linear, with m_k = 0 allowed; reason: this covers every isometric Φ with m_k ≥ 1; a block with m_k = 0 is the zero space
--   - encoding: U = ⨁ 𝟙 ⊗ U_k and C(U) = ⨁ B ⊗ 𝟙, equalities after a change of basis → the identification Φ; reason: Lean needs the identification explicit; (31)–(32) state the same thing in matrices
--   - encoding: bounded operators B_{m_k} on an m_k-dimensional Hilbert space → linear maps on EuclideanSpace ℂ (Fin (m k)); reason: every linear map on a finite dimensional space is bounded
--   - encoding: irreducible (Def 13, read literally, also admits V = 0) → Representation.IsIrreducible, which requires a nonzero space; reason: Mathlib convention; a zero summand adds nothing, and V = 0 has the empty decomposition
-- source:
--   Ragone et al., Representation Theory for Geometric Quantum Machine Learning, arXiv:2210.07980v2, Theorem 7, p.28, with (31)–(32), p.29

import Mathlib
import Definitions.Def_RepGQML_commutant
import Definitions.Def_RepGQML_groupAlgebra
import Definitions.Def_RepGQML_IsIrrepDecomposition

namespace RepGQML

/-- **Theorem 7, commutant structure** (Ragone et al., *Representation Theory for Geometric Quantum Machine Learning*, arXiv:2210.07980v2, p.28). Let `U` be a unitary representation of a group
`G` on a finite dimensional complex Hilbert space `H`. Then:

1. `U` has a decomposition `U = ⨁_{k=1}^K 𝟙_{m_k} ⊗ U_k` into pairwise inequivalent irreducible
   unitary representations with multiplicities `m_k ≥ 1`, through an isometry `Φ`;
2. for every decomposition `Φ`, an operator `T` lies in the commutant `C(U)` if and only if there are
   operators `B_k` on `ℂ^{m_k}` with `Φ T Φ⁻¹ = ⨁_k B_k ⊗ 𝟙_{dim U_k}`.

**Formalization Note** Compactness of `G` is not assumed: the statement holds for any group, and a
compact group with a continuous `U` is an instance. The field is `ℂ`: for `SO(2)` on `ℝ²` the
representation is irreducible and the commutant is `ℂ`, not `ℝ`. Finite dimension is the standing
restriction of §VII.C (p.27). Clause 2 takes `Φ` only linear, which covers the isometric `Φ` of clause 1.
Every linear operator on a finite dimensional space is bounded, so "bounded operators" needs no
analytic condition. -/
theorem commutant_structure {G H : Type*} [Group G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (U : Representation ℂ G H)
    (hU : IsUnitaryRep U) :
    (∃ (n : ℕ) (m d : Fin n → ℕ)
        (ρ : ∀ k, Representation ℂ G (EuclideanSpace ℂ (Fin (d k))))
        (Φ : H ≃ₗᵢ[ℂ] IrrepSum m fun k => EuclideanSpace ℂ (Fin (d k))),
        (∀ k, 1 ≤ m k) ∧ IsIrrepDecomposition U m (fun k => EuclideanSpace ℂ (Fin (d k))) ρ
          Φ.toLinearEquiv) ∧
    ∀ {K : Type*} [Fintype K] (m : K → ℕ) (V : K → Type*) [∀ k, NormedAddCommGroup (V k)]
      [∀ k, InnerProductSpace ℂ (V k)] [∀ k, FiniteDimensional ℂ (V k)]
      (ρ : ∀ k, Representation ℂ G (V k)) (Φ : H ≃ₗ[ℂ] IrrepSum m V),
      IsIrrepDecomposition U m V ρ Φ →
      ∀ T : Module.End ℂ H, T ∈ commutant (groupAlgebra U) ↔
        ∃ B : ∀ k, Module.End ℂ (EuclideanSpace ℂ (Fin (m k))),
          ∀ (x : H) (k : K), Φ (T x) k = TensorProduct.map (B k) LinearMap.id (Φ x k) := by sorry

end RepGQML
