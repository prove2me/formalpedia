-- Prove2me | Theorems.Thm_PadicAlgCl_dvd_valuation_of_smul_kummerCocycle_pairing_mem_levelCoboundaries2
-- name    : PadicAlgCl.dvd_valuation_of_smul_kummerCocycle_pairing_mem_levelCoboundaries2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/835a42ab-ca22-5a0b-89fa-2082ed88a822
-- title:
--   Level coboundary of χ∪κ_α forces p ∣ vₚ(a)
-- statement:
--   Fix a prime $p$, an element $\zeta$ of $\overline{\mathbb{Q}}$ which is a primitive $p$-th root of unity, and a function $\chi$ from the group of $\mathbb{Q}_p$-algebra automorphisms of `PadicAlgCl p` to $\mathbb{Z}$. Assume: $\chi$ satisfies the predicate [`groupCohomology.IsLevelConstant₁`](def/GroupCohomology_ContinuousH2.html#L14) relative to the homomorphism [`localGaloisToGlobal p`](def/GaloisRep_CompletionBridge.html#L41), which sends an automorphism of `PadicAlgCl p` over $\mathbb{Q}_p$ to the restriction of its underlying $\mathbb{Q}$-algebra automorphism to the normal subextension $\overline{\mathbb{Q}}$; $p \mid \chi(\sigma)+\chi(\tau)-\chi(\sigma\tau)$ for all $\sigma,\tau$, so that $\chi$ reduces to an additive character mod $p$; and for every $\sigma$, the condition that $\sigma$ fixes every $w$ with $w^{p^p-1}=1$ is equivalent to $p \mid \chi(\sigma)$. Let $\varphi$ be an automorphism with $\varphi(w)=w^p$ for all such $w$, let $a \in \mathbb{Q}_p^\times$ and $\alpha$ a unit of `PadicAlgCl p` with $a = \alpha^p$ in `PadicAlgCl p`. Suppose finally that the $2$-cochain sending $(g_1,g_2)$ to the element $g_1(g_2\alpha/\alpha)^{\chi(g_1)}$ of the group $\mu_p$ of `PadicAlgCl p`, pushed into the (additively written) unit group via `Rep.ofAlgebraAutOnUnits ℚ_[p] (PadicAlgCl p)`, lies in [`groupCohomology.levelCoboundaries₂`](def/GroupCohomology_ContinuousH2.html#L92) for [`localGaloisToGlobal p`](def/GaloisRep_CompletionBridge.html#L41). Then $p$ divides the $p$-adic valuation of $a$.
--
--   This is the Galois-cohomological form of the classical computation of the norm residue symbol against an unramified character of order $p$, $(\chi,a)_p = \chi(\mathrm{Frob})^{v_p(a)}$: triviality of the cup product $\chi \cup \kappa_a$ forces $v_p(a) \equiv 0 \bmod p$. It feeds the local obstruction step used by [`PadicAlgCl.exists_isUnit_forall_dvd_valuation_of_thickening`](thm.html#PadicAlgCl.exists_isUnit_forall_dvd_valuation_of_thickening).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicAlgCl_dvd_valuation_of_smul_kummerCocycle_pairing_mem_levelCoboundaries2.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_Kummer
import Definitions.Def_GaloisRep_CompletionBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PadicAlgCl.dvd_valuation_of_smul_kummerCocycle_pairing_mem_levelCoboundaries2
    (p : ℕ) [Fact p.Prime] (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
    (χ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → ℤ) (hχlc : groupCohomology.IsLevelConstant₁ (localGaloisToGlobal p) χ)
    (hχ : ∀ σ τ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), (p : ℤ) ∣ χ σ + χ τ - χ (σ * τ))
    (hKχ : ∀ σ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), (∀ w : PadicAlgCl p, w ^ (p ^ p - 1) = 1 → σ w = w) ↔ (p : ℤ) ∣ χ σ)
    (φ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) (hφ : ∀ w : PadicAlgCl p, w ^ (p ^ p - 1) = 1 → φ w = w ^ p)
    (a : ℚ_[p]ˣ) (α : (PadicAlgCl p)ˣ)
    (hα : algebraMap ℚ_[p] (PadicAlgCl p) (a : ℚ_[p]) = (α : PadicAlgCl p) ^ p)
    (hcob : (fun g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) × (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) =>
        (MonoidHom.toAdditive (rootsOfUnity p (PadicAlgCl p)).subtype).toIntLinearMap
          ((χ g.1) • (groupCohomology.Kummer.kummerRep ℚ_[p] (PadicAlgCl p) p).ρ g.1
            (Additive.ofMul (groupCohomology.Kummer.kummerCocycleRoots hα g.2))))
      ∈ groupCohomology.levelCoboundaries₂ (localGaloisToGlobal p)
          (Rep.ofAlgebraAutOnUnits ℚ_[p] (PadicAlgCl p))) :
    (p : ℤ) ∣ Padic.valuation (a : ℚ_[p]) := by sorry
