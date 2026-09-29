-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_hasLowerLevelTorsion_jZero_of_twoNewEigenformCongruence_sqf_five
-- name    : WeierstrassCurve.exists_hasLowerLevelTorsion_jZero_of_twoNewEigenformCongruence_sqf_five
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/050ca0a2-b225-580e-b9b4-94f52b6ca357
-- title:
--   Interchange step of Ribet level lowering on J₀(Nq')
-- statement:
--   Let $W$ be a Weierstrass equation over $\mathbb{Z}$ and $p$ a prime such that the representation of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on the $p$-torsion of $W$ base-changed to $\mathbb{Q}$ (inside $\overline{\mathbb{Q}}=$ `AlgebraicClosure ℚ`) is irreducible. Let $N>0$ and let $q,q'$ be primes with $q'\ge 5$, $q'\ne q$, $q'\ne p$, neither dividing $N$, with $N$ squarefree, $q\equiv 1$ and $q'\not\equiv 1$ in $\mathbb{Z}/p$, with $q'\nmid\Delta(W)$, and with the $p$-torsion representation unramified at $q$, i.e. for every valuation subring of $\overline{\mathbb{Q}}$ lying over $q$, every element of its inertia subgroup over $\mathbb{Q}$ fixes each $p$-torsion point. Let $g$ be a weight-two cusp form on $\Gamma_0(Nqq')$ which is a normalised eigenform in the sense of having $a_1(g)=1$, multiplicative coefficients at coprime arguments and the usual prime-power recursions inside and outside the level, and which satisfies $a_q(g)^2=1$ and $a_{q'}(g)^2=1$. Let $k$ be a finite field, $\mathcal{O}\subseteq\mathbb{C}$ a subring containing every $a_\ell(g)$ ($\ell$ prime) and $\varphi:\mathcal{O}\to k$ a ring homomorphism; let $\mathfrak{m}\subset\mathbb{T}=\mathbb{Z}[T_\ell:\ell\ \text{prime}]$ be the kernel of $T_\ell\mapsto\varphi(a_\ell(g))$, assumed maximal and containing $p$, and assume $\varphi(a_\ell(g))=a_\ell(W)$ in $k$ for every prime $\ell\nmid Nqq'$ with $\ell\ne p$ and $\ell\nmid\Delta(W)$, where $a_\ell(W)$ is the trace of Frobenius of the reduction of $W$ modulo $\ell$. Then, for the Hecke action of $\mathbb{T}$ on $J_0(Nq')=\mathrm{Pic}^0$ of the level-$Nq'$ modular function field over $\overline{\mathbb{Q}}$, there is a finite set $S$ of primes, each dividing $Nqq'$, and a nonzero $y\in J_0(Nq')$ killed by every integer lying in $\mathfrak{m}$ and by every $T_\ell-b$ ($b\in\mathbb{Z}$) lying in $\mathfrak{m}$ with $\ell\notin S$.
--
--   This is the interchange step in Ribet's level lowering in the case $q\equiv 1 \pmod p$: the eigensystem attached to $g$ at level $Nqq'$, congruent mod $\mathfrak{m}$ to the $p$-torsion of $W$, is shown to reappear in the Jacobian of the lower level $Nq'$, away from the primes of the level. It is used in the passage to a residually modular form of smaller level, cited by [`WeierstrassCurve.isResiduallyModularOfLevel_div_of_cast_eq_one_of_isUnramifiedAt_sqf`](thm.html#WeierstrassCurve.isResiduallyModularOfLevel_div_of_cast_eq_one_of_isUnramifiedAt_sqf).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_hasLowerLevelTorsion_jZero_of_twoNewEigenformCongruence_sqf_five.lean

import Definitions.Def_FreyPackage_LevelRaising
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_MazurPrincipleCore

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

theorem WeierstrassCurve.exists_hasLowerLevelTorsion_jZero_of_twoNewEigenformCongruence_sqf_five
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime]
    (hirr : W.ModRepIsIrreducible p) {N q q' : ℕ}
    (hN : 0 < N) (hq : q.Prime) (hq' : q'.Prime) (hq'5 : 5 ≤ q') (hqN : ¬ q ∣ N) (hqq' : q' ≠ q) (hq'p : q' ≠ p)
    (hq'N : ¬ q' ∣ N) [NeZero (N * q')] (hNsq : Squarefree N)
    (hq1 : ((q : ℕ) : ZMod p) = 1) (hq'1 : ((q' : ℕ) : ZMod p) ≠ 1)
    (hq'good : W.IsGoodPrimeFor q')
    (hunr : WeierstrassCurve.Affine.Point.GaloisRepUnramifiedAt (K := AlgebraicClosure ℚ) ℚ
      (W.map (Int.castRingHom ℚ)) p q)
    (g : CuspForm (CongruenceSubgroup.Gamma0 (N * q * q')) 2)
    (hg : g.IsNormalizedEigenform) (hgq : g.IsNewAt q) (hgq' : g.IsNewAt q')
    (k : Type) [Field k] [Finite k] (𝒪 : Subring ℂ)
    (h𝒪 : ∀ ℓ : Nat.Primes, ModularFormClass.qCoeff g ℓ ∈ 𝒪) (φ : 𝒪 →+* k)
    (hmax : (eigenIdeal (fun ℓ => φ ⟨ModularFormClass.qCoeff g ℓ, h𝒪 ℓ⟩)).IsMaximal)
    (hp : (p : HeckeAlg) ∈ eigenIdeal (fun ℓ => φ ⟨ModularFormClass.qCoeff g ℓ, h𝒪 ℓ⟩))
    (hcong : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ N * q * q' → ℓ ≠ p →
        φ ⟨ModularFormClass.qCoeff g ℓ, h𝒪 ⟨ℓ, hℓ⟩⟩ = ((W.apOfModel ℓ : ℤ) : k)) :
    letI := heckeModuleBar (N * q')
    ∃ S : Finset Nat.Primes, (∀ ℓ ∈ S, (ℓ : ℕ) ∣ N * q * q') ∧
      HasLowerLevelTorsion S (eigenIdeal (fun ℓ => φ ⟨ModularFormClass.qCoeff g ℓ, h𝒪 ℓ⟩))
        (JZero (N * q')) := by sorry
