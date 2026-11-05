-- Prove2me | Theorems.Thm_RepGQML_schur_lemma
-- name    : RepGQML.schur_lemma
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:46:17.589001+00:00
-- url     : https://prove2.me/theorems/221e54bf-9ec8-4e66-a787-a7df275552e1
-- title:
--   Theorem 6 — Schur's lemma for groups and Lie algebras (corrected: the scalar clause is for one representation, in finite dimension)
-- statement:
--   Let $V$ and $W$ be complex vector spaces, and let $\rho,\sigma$ be representations on them of a group $G$, or of a Lie algebra $\mathfrak g$. Assume irreducibility as needed below. Then:
--
--   1. if $\rho$ and $\sigma$ are irreducible, an equivariant map $\varphi:V\to W$ is either $0$, or is bijective and then $V\cong W$ as representations;
--   2. if $\rho$ is irreducible and $V$ is finite dimensional, an equivariant map $\varphi:V\to V$ from $\rho$ to itself equals $\lambda\mathbb 1$ for some $\lambda\in\mathbb C$;
--   3. if $\rho,\sigma$ are irreducible and equivalent and $V$ is finite dimensional, there is a nonzero equivariant $\varphi_0:V\to W$, and every equivariant map $V\to W$ is a scalar multiple of it. So the space of equivariant maps is one dimensional.
--
--   All three hold for a group and for a Lie algebra. Schur's lemma is what makes the commutant in Theorem 7 act only on multiplicities.
--
--   **Formalization Note** A Lie algebra representation is an additive bracket-preserving map on a `LieRing`, see `IsLieRep`. Clause 1 needs no finite dimension.
--
--   Differences from the source:
--   - correction: If φ : V → W is an isomorphism, it must be that φ = λ𝟙 → an equivariant endomorphism of one representation is λ𝟙 (clause 2), and between equivalent irreps the equivariant maps form a line (clause 3), which is the gloss on p.25; reason: the printed clause is false for two representations on one space: with R irreducible on ℂ² and S_g = D R_g D⁻¹, D = diag(1, 2), the map D is an equivariant isomorphism R → S and is not scalar
--   - correction: the scalar clause, for a group representation of any dimension (Def 6) → finite dimensional V in clauses 2 and 3; reason: without it the clause is false: G = ℂ(x)^× acts on V = ℂ(x) by multiplication, irreducibly since invariant ℂ-subspaces are ℂ(x)-subspaces, and multiplication by x is equivariant, bijective and not scalar
--   - generalization: a Lie algebra g with a linear r on a finite dimensional V (Def 7) → a LieRing with an additive bracket-preserving r on a complex space, and finite dimension only in clauses 2 and 3; reason: a real or complex Lie algebra is a LieRing and a linear map is additive, so the source case specializes, including su(2) acting on a complex space
--   - generalization: a group or Lie group → any group; reason: a Lie group is a group
--   - encoding: irreducible (Def 13, read literally, also admits V = 0) → Representation.IsIrreducible, which requires a nonzero space; reason: Mathlib convention; a zero summand adds nothing, and V = 0 has the empty decomposition
-- source:
--   Ragone et al., Representation Theory for Geometric Quantum Machine Learning, arXiv:2210.07980v2, Theorem 6, p.25, with the gloss on p.25

import Mathlib
import Definitions.Def_RepGQML_AreEquivalent
import Definitions.Def_RepGQML_IsLieRep
import Definitions.Def_RepGQML_IsLieIrreducible
import Definitions.Def_RepGQML_AreLieEquivalent

namespace RepGQML

/-- **Theorem 6, Schur's lemma** (Ragone et al., *Representation Theory for Geometric Quantum Machine Learning*, arXiv:2210.07980v2, p.25), with its gloss on the same page, for a group and for a
Lie algebra. For irreducible complex representations:

(a) an equivariant map `φ : V → W` is `0`, or it is an isomorphism and `V ≅ W`;
(b) if `V` is finite dimensional, an equivariant map from a representation to itself is `λ𝟙`;
(c) if `V` is finite dimensional and `V ≅ W`, the equivariant maps `V → W` form a one dimensional
space, the multiples of a nonzero `φ₀`.

**Formalization Note** The page prints "If `φ : V → W` is an isomorphism, it must be that `φ = λ𝟙`",
with `V ≠ W` as representations allowed; (b) and (c) are the corrected forms (see the
natural-language statement for the counterexamples). Clause (a) needs no finite dimension. The Lie
algebra representation is an additive bracket-preserving map on a `LieRing` (see `IsLieRep`). -/
theorem schur_lemma {G L V W : Type*} [Group G] [LieRing L] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (r : L →+ Module.End ℂ V) (s : L →+ Module.End ℂ W) :
    (ρ.IsIrreducible → σ.IsIrreducible → ∀ φ : V →ₗ[ℂ] W, IsEquivariant ρ σ φ →
        φ = 0 ∨ (Function.Bijective φ ∧ AreEquivalent ρ σ)) ∧
    (ρ.IsIrreducible → FiniteDimensional ℂ V → ∀ φ : V →ₗ[ℂ] V, IsEquivariant ρ ρ φ →
        ∃ c : ℂ, φ = c • LinearMap.id) ∧
    (ρ.IsIrreducible → σ.IsIrreducible → FiniteDimensional ℂ V → AreEquivalent ρ σ →
        ∃ φ₀ : V →ₗ[ℂ] W, φ₀ ≠ 0 ∧ IsEquivariant ρ σ φ₀ ∧
          ∀ ψ : V →ₗ[ℂ] W, IsEquivariant ρ σ ψ → ∃ c : ℂ, ψ = c • φ₀) ∧
    (IsLieRep r → IsLieRep s → IsLieIrreducible r → IsLieIrreducible s →
      ∀ φ : V →ₗ[ℂ] W, IsLieEquivariant r s φ →
        φ = 0 ∨ (Function.Bijective φ ∧ AreLieEquivalent r s)) ∧
    (IsLieRep r → IsLieIrreducible r → FiniteDimensional ℂ V →
      ∀ φ : V →ₗ[ℂ] V, IsLieEquivariant r r φ → ∃ c : ℂ, φ = c • LinearMap.id) ∧
    (IsLieRep r → IsLieRep s → IsLieIrreducible r → IsLieIrreducible s →
      FiniteDimensional ℂ V → AreLieEquivalent r s →
        ∃ φ₀ : V →ₗ[ℂ] W, φ₀ ≠ 0 ∧ IsLieEquivariant r s φ₀ ∧
          ∀ ψ : V →ₗ[ℂ] W, IsLieEquivariant r s ψ → ∃ c : ℂ, ψ = c • φ₀) := by sorry

end RepGQML
