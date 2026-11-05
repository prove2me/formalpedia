-- Prove2me | Theorems.Thm_RepGQML_no_mixing
-- name    : RepGQML.no_mixing
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:45:32.537126+00:00
-- url     : https://prove2.me/theorems/7b52f8cc-8c30-4997-b2eb-e3fe7c98a524
-- title:
--   Footnote 20 — multiples of inequivalent irreps do not mix
-- statement:
--   Let $\rho$ and $\sigma$ be irreducible, inequivalent complex representations of a group $G$ on $V$ and $V'$. If a linear map $T:\mathbb C^{m}\otimes V\to\mathbb C^{m'}\otimes V'$ satisfies
--   $$
--   T\circ(\mathbb 1_{m}\otimes\rho_g)=(\mathbb 1_{m'}\otimes\sigma_g)\circ T\qquad\text{for all }g\in G,
--   $$
--   then $T=0$.
--
--   This is why the commutant in Theorem 7 cannot connect different irreps.
--
--   Differences from the source:
--   - reading: Schur's lemma "guarantees that inequivalent representations do not mix" → an intertwiner between 𝟙_m ⊗ ρ and 𝟙_m' ⊗ σ with ρ, σ inequivalent irreps is 0; reason: the sentence is informal; this is its precise form for the blocks of Theorem 7
--   - generalization: unitary representations of a compact group, finite dimensional → irreducible complex representations of any group, in any dimension; reason: unitarity, compactness and finite dimension play no part; the source case specializes
--   - encoding: irreducible (Def 13, read literally, also admits V = 0) → Representation.IsIrreducible, which requires a nonzero space; reason: Mathlib convention; a zero summand adds nothing, and V = 0 has the empty decomposition
-- source:
--   Ragone et al., Representation Theory for Geometric Quantum Machine Learning, arXiv:2210.07980v2, footnote 20, p.28, and p.29

import Mathlib
import Definitions.Def_RepGQML_AreEquivalent

namespace RepGQML

open scoped TensorProduct in
/-- Inequivalent irreps do not mix (Ragone et al., *Representation Theory for Geometric Quantum Machine Learning*, arXiv:2210.07980v2, footnote 20, p.28, and p.29): if `ρ`, `σ` are irreducible
and inequivalent, every map `ℂ^m ⊗ V → ℂ^{m'} ⊗ V'` intertwining `𝟙 ⊗ ρ_g` and `𝟙 ⊗ σ_g` is zero.

**Formalization Note** The sentence on the page is informal. This is its precise form for the
blocks of Theorem 7, with the multiplicity factor first. -/
theorem no_mixing {G V V' : Type*} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V']
    [Module ℂ V'] (ρ : Representation ℂ G V) (σ : Representation ℂ G V')
    (hρ : ρ.IsIrreducible) (hσ : σ.IsIrreducible) (hne : ¬ AreEquivalent ρ σ) (m m' : ℕ)
    (T : EuclideanSpace ℂ (Fin m) ⊗[ℂ] V →ₗ[ℂ] EuclideanSpace ℂ (Fin m') ⊗[ℂ] V')
    (hT : ∀ g : G, T ∘ₗ TensorProduct.map LinearMap.id (ρ g) =
      TensorProduct.map LinearMap.id (σ g) ∘ₗ T) :
    T = 0 := by sorry

end RepGQML
