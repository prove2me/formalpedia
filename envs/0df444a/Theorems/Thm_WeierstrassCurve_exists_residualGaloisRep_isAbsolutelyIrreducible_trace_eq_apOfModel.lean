-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_residualGaloisRep_isAbsolutelyIrreducible_trace_eq_apOfModel
-- name    : WeierstrassCurve.exists_residualGaloisRep_isAbsolutelyIrreducible_trace_eq_apOfModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/b6cd8cb4-4345-5626-9d25-f350fcf431c2
-- title:
--   Mod-p representation of a semistable model: irreducibility and Frobenius traces
-- statement:
--   Let $p$ be a prime with $p \neq 2$ and let $W$ be a Weierstrass curve over $\mathbb{Z}$ with $\Delta_W \neq 0$ which is a semistable model, i.e. no prime dividing $\Delta_W$ divides $c_4(W)$, and whose mod-$p$ representation is irreducible in the sense that the $p$-torsion of the points of $W_{\mathbb{Q}}$ over $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` is non-trivial and its only Galois-stable $\mathbb{Z}/p$-submodules are $0$ and the whole module. Then there exist a field $k$ of characteristic $p$ and a residual Galois representation $\bar\rho$ over $k$ — a $k$-vector space $V$ of dimension $2$ together with a monoid homomorphism from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ (the $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}}$) to $\mathrm{End}_k V$ that is trivial on the automorphisms fixing some finite extension of $\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ — such that: (i) the base change of $\bar\rho$ to $\mathrm{AlgebraicClosure}\,k$ has no stable subspace other than $0$ and the whole space; (ii) if $p = 3$, then for every field $K$ that is a $k$-algebra and every index-two subgroup $G$ of the Galois group, every $K$-submodule of $K \otimes_k V$ stable under all $\bar\rho(\sigma)$, $\sigma \in G$, is $0$ or everything; and (iii) for every prime $\ell \neq p$ with $\ell \nmid \Delta_W$, every valuation subring $A$ of $\overline{\mathbb{Q}}$ in which $\ell$ is a non-unit, and every $\sigma$ lying in the decomposition subgroup of $A$ over $\mathbb{Q}$ and acting on the residue field of $A$ by $x \mapsto x^{\ell}$, one has $\mathrm{tr}\,\bar\rho(\sigma) = a_{\ell}(W)$ in $k$, where $a_{\ell}(W) = \ell + 1 - \#W(\mathbb{Z}/\ell)$ is computed from the reduction of $W$ modulo $\ell$.
--
--   This packages the mod-$p$ Galois representation attached to a semistable integral Weierstrass model as the input datum required by the modularity-lifting and level-lowering arguments: absolute irreducibility, the absence of a line stable under an index-two subgroup when $p = 3$, and the identification of Frobenius traces at the good primes with the integers $a_\ell(W)$. It is used in the production of a normalised eigenform, respectively a parabolic cohomology class, of the expected level and Hecke eigenvalues.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_residualGaloisRep_isAbsolutelyIrreducible_trace_eq_apOfModel.lean

import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.exists_residualGaloisRep_isAbsolutelyIrreducible_trace_eq_apOfModel
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (hW : W.IsSemistableModel) (hirr : W.ModRepIsIrreducible p) :
    ∃ (k : Type) (_ : Field k) (_ : CharP k p) (ρbar : ResidualGaloisRep k),
      ρbar.IsAbsolutelyIrreducible ∧
      (p = 3 → ∀ (K : Type) [Field K] [Algebra k K]
        (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
          ∀ V : Submodule K (ρbar.baseChange K).V,
            (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤) ∧
      ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            LinearMap.trace k ρbar.V (ρbar.ρ σ) = (W.apOfModel ℓ : k) := by sorry
