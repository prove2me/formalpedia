-- Prove2me | Theorems.Thm_RepGQML_exists_irrepDecomposition
-- name    : RepGQML.exists_irrepDecomposition
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:46:36.230509+00:00
-- url     : https://prove2.me/theorems/c5b814c7-e472-4c98-8154-4e5e4600a740
-- title:
--   p.28 — every finite dimensional unitary representation has the form $\bigoplus_k\mathbb 1_{m_k}\otimes U_k$
-- statement:
--   Let $U$ be a unitary representation of a group $G$ on a finite dimensional complex Hilbert space $H$. Then there are an integer $K$, multiplicities $m_k\ge 1$, dimensions $d_k$, pairwise inequivalent irreducible unitary representations $U_k$ of $G$ on $\mathbb C^{d_k}$, and a surjective linear isometry
--   $$
--   \Phi:H\longrightarrow\bigoplus_{k=1}^K\mathbb C^{m_k}\otimes\mathbb C^{d_k}
--   $$
--   that carries $U_g$ to $\bigoplus_k\mathbb 1_{m_k}\otimes(U_k)_g$.
--
--   This is what "its decomposition into irreps" in Theorem 7 presupposes.
--
--   **Formalization Note** The irreps are stated as unitary matrix representations on $\mathbb C^{d_k}$, matching the matrix representatives of (31). When $H=0$ the index set is empty.
--
--   Differences from the source:
--   - reading: Theorem 7 presupposes a decomposition; p.23 and p.28 describe it → existence of the decomposition with pairwise inequivalent irreps and m_k ≥ 1; reason: the source takes this for granted; this is the statement that supplies it
--   - generalization: a compact group → any group; reason: compactness is used in the source only to get unitarity (Theorem 5), which is assumed here
--   - encoding: irreps U_k on abstract spaces → unitary matrix representations on ℂ^{d_k}; reason: every finite dimensional unitary irrep is unitarily equivalent to one of these, by an orthonormal basis
--   - encoding: U = ⨁ 𝟙 ⊗ U_k, an equality after a change of basis → an isometry Φ; reason: Lean needs the identification explicit; (31) is the same statement in matrices
--   - encoding: irreducible (Def 13, read literally, also admits V = 0) → Representation.IsIrreducible, which requires a nonzero space; reason: Mathlib convention; a zero summand adds nothing, and V = 0 has the empty decomposition
-- source:
--   Ragone et al., Representation Theory for Geometric Quantum Machine Learning, arXiv:2210.07980v2, p.28, "the expression 𝟙_{m_k} ⊗ U_k", with Theorem 4, p.23, and (31), p.29

import Mathlib
import Definitions.Def_RepGQML_IsIrrepDecomposition

namespace RepGQML

/-- Every finite dimensional unitary representation of a group on a complex Hilbert space has the
form `U = ⨁_{k=1}^K 𝟙_{m_k} ⊗ U_k` with `U_k` pairwise inequivalent irreducible unitary
representations and `m_k ≥ 1`, through an isometric identification (Ragone et al., *Representation Theory for Geometric Quantum Machine Learning*, arXiv:2210.07980v2, p.28, the expression
`𝟙_{m_k} ⊗ U_k`, with Theorem 4, p.23).

**Formalization Note** The `U_k` are taken as unitary matrix representations on `ℂ^{d_k}`, matching the
"matrix representatives" of (31), p.29. Any unitary irrep is unitarily equivalent to one of these. -/
theorem exists_irrepDecomposition {G H : Type*} [Group G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (U : Representation ℂ G H)
    (hU : IsUnitaryRep U) :
    ∃ (n : ℕ) (m d : Fin n → ℕ)
        (ρ : ∀ k, Representation ℂ G (EuclideanSpace ℂ (Fin (d k))))
        (Φ : H ≃ₗᵢ[ℂ] IrrepSum m fun k => EuclideanSpace ℂ (Fin (d k))),
        (∀ k, 1 ≤ m k) ∧ IsIrrepDecomposition U m (fun k => EuclideanSpace ℂ (Fin (d k))) ρ
          Φ.toLinearEquiv := by sorry

end RepGQML
