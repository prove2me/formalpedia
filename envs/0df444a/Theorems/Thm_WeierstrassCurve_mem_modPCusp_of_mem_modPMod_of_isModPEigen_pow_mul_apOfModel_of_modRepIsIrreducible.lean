-- Prove2me | Theorems.Thm_WeierstrassCurve_mem_modPCusp_of_mem_modPMod_of_isModPEigen_pow_mul_apOfModel_of_modRepIsIrreducible
-- name    : WeierstrassCurve.mem_modPCusp_of_mem_modPMod_of_isModPEigen_pow_mul_apOfModel_of_modRepIsIrreducible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/79fe507d-7028-5966-a20b-68128fcc73bc
-- title:
--   Mod-p eigenforms with elliptic curve eigenvalues are cuspidal
-- statement:
--   Let $p$ be a prime with $p \neq 2$, and let $W$ be a Weierstrass curve over $\mathbb{Z}$ with $\Delta_W \neq 0$ whose mod-$p$ representation is irreducible in the sense of `ModRepIsIrreducible`: the $p$-torsion submodule of the group of points of $W$ base-changed to $\overline{\mathbb{Q}}$ is nontrivial, and every $\mathbb{Z}/p$-submodule of it that is stable under the Galois action of $\mathbb{Q}$ is $\bot$ or $\top$. Let $N' \neq 0$ with $p \nmid N'$, let $S_0$ be a finite set of naturals with $p \in S_0$, let $k' \geq 2$ be an integer, $j$ a natural number, $F$ a field of characteristic $p$, $\psi$ a power series over $F$ and $\mathrm{mu} : \mathbb{N} \to F$. Assume $\psi$ lies in `modPMod N' k' F`, the $F$-span of the series obtained by reducing into $F$ the integral $q$-expansion coefficients of modular forms of weight $k'$ on $\Gamma_0(N')$; assume $\psi \neq 0$ and that for every prime $\ell \nmid N'$ with $\ell \notin S_0$ one has $\mathrm{heckePS}\,k'\,\ell\,\psi = \mathrm{mu}(\ell) \cdot \psi$, where the $n$-th coefficient of $\mathrm{heckePS}\,k'\,\ell\,\psi$ is $\psi_{n\ell} + \ell^{k'-1}\psi_{n/\ell}$ if $\ell \mid n$ and $\psi_{n\ell}$ otherwise; and assume that for every prime $\ell \notin S_0$ with $\ell \nmid N'$ and $(\ell : \mathbb{Z}) \nmid \Delta_W$ the eigenvalue is $\mathrm{mu}(\ell) = \ell^{j} a_\ell(W)$ in $F$, where $a_\ell(W)$ is the trace of Frobenius $\ell + 1 - \#W(\mathbb{Z}/\ell)$ of the reduction of $W$ modulo $\ell$. Then $\psi$ lies in `modPCusp N' k' F`, the $F$-span of the reductions into $F$ of integral $q$-expansions of cusp forms of weight $k'$ on $\Gamma_0(N')$.
--
--   This is the mod-$p$ Eisenstein alternative in the form needed for level lowering: an eigen-$q$-expansion in characteristic $p$ whose Hecke eigenvalues are a fixed power of $\ell$ times the Frobenius traces of an elliptic curve with irreducible mod-$p$ representation cannot be Eisenstein, hence is cuspidal. It feeds the cuspidality step in the construction of a maximal ideal of the cusp-form Hecke algebra matching $W$ modulo $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_mem_modPCusp_of_mem_modPMod_of_isModPEigen_pow_mul_apOfModel_of_modRepIsIrreducible.lean

import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_ModularRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModPForms

theorem WeierstrassCurve.mem_modPCusp_of_mem_modPMod_of_isModPEigen_pow_mul_apOfModel_of_modRepIsIrreducible
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ)
    (hΔ : W.Δ ≠ 0) (hirr : W.ModRepIsIrreducible p)
    (N' : ℕ) [NeZero N'] (hpN' : ¬ p ∣ N') (S₀ : Set ℕ) (hS₀fin : S₀.Finite) (hS₀p : p ∈ S₀)
    (k' : ℤ) (hk' : 2 ≤ k') (j : ℕ)
    (F : Type) [Field F] [CharP F p]
    (ψ : PowerSeries F) (mu : ℕ → F)
    (hψ : ψ ∈ modPMod N' k' F) (heig : IsModPEigen N' S₀ k' ψ mu)
    (hmu : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → ¬ ℓ ∣ N' → W.IsGoodPrimeFor ℓ →
      mu ℓ = ((ℓ ^ j * W.apOfModel ℓ : ℤ) : F)) :
    ψ ∈ modPCusp N' k' F := by sorry
