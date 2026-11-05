-- Prove2me | Theorems.Thm_RepGQML_exists_unitary_equivalence
-- name    : RepGQML.exists_unitary_equivalence
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:45:50.212304+00:00
-- url     : https://prove2.me/theorems/d8d7bed5-54ef-400b-908c-88bb21e4dc5f
-- title:
--   p.27 (implicit) — equivalent irreducible unitary representations are unitarily equivalent
-- statement:
--   Let $\rho$ and $\sigma$ be irreducible unitary representations of a group $G$ on finite dimensional complex inner product spaces $V$ and $W$. If $\rho$ and $\sigma$ are equivalent, there is a surjective linear isometry $e:V\to W$ with
--   $$
--   e\circ\rho_g=\sigma_g\circ e\qquad\text{for all } g\in G.
--   $$
--
--   The source does not state this. It is what lets a decomposition into irreps be an identification of Hilbert spaces, so that the blocks of (31) are unitary.
--
--   Differences from the source:
--   - reading: no printed statement: p.27 treats block diagonalization of unitary representations as a change of basis between unitary representatives → equivalent irreducible unitary representations are unitarily equivalent; reason: this is the implicit fact needed for clause 1 of the goal to give an isometry
--   - generalization: a compact group → any group; reason: compactness plays no part
--   - encoding: irreducible (Def 13, read literally, also admits V = 0) → Representation.IsIrreducible, which requires a nonzero space; reason: Mathlib convention; a zero summand adds nothing, and V = 0 has the empty decomposition
-- source:
--   Ragone et al., Representation Theory for Geometric Quantum Machine Learning, arXiv:2210.07980v2, p.27, the paragraph opening §VII.C (implicit there)

import Mathlib
import Definitions.Def_RepGQML_IsUnitaryRep
import Definitions.Def_RepGQML_AreEquivalent

namespace RepGQML

/-- Equivalent irreducible unitary representations are unitarily equivalent. This is implicit in
Ragone et al., *Representation Theory for Geometric Quantum Machine Learning*, arXiv:2210.07980v2, p.27, and it is what lets the decomposition of Theorem 7 be an identification of Hilbert
spaces. -/
theorem exists_unitary_equivalence {G V W : Type*} [Group G] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (hρ : ρ.IsIrreducible) (hσ : σ.IsIrreducible) (hρu : IsUnitaryRep ρ) (hσu : IsUnitaryRep σ)
    (h : AreEquivalent ρ σ) :
    ∃ e : V ≃ₗᵢ[ℂ] W, ∀ (g : G) (v : V), e (ρ g v) = σ g (e v) := by sorry

end RepGQML
