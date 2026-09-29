-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_H1_bot_ne_zero_parabolic_diamondRaw_eq_heckeT_eq_smul_of_isEigensystemH1_one
-- name    : WeierstrassCurve.exists_H1_bot_ne_zero_parabolic_diamondRaw_eq_heckeT_eq_smul_of_isEigensystemH1_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/b306b4dc-45ce-5ee2-acc8-2496590d96f8
-- title:
--   Parabolic diamond-invariant H¹(Γ₁(N)) class with eigenvalues a_ℓ(W)
-- statement:
--   Let $p$ be an odd prime and let $W$ be a Weierstrass curve over $\mathbb{Z}$ with $\Delta_W \neq 0$ whose mod $p$ representation is irreducible in the sense of `ModRepIsIrreducible`, i.e. the $p$-torsion of the base change of $W$ to $\mathbb{Q}$, taken in the points over $\overline{\mathbb{Q}}$, is nontrivial and every Galois-stable $\mathbb{Z}/p$-submodule of it is $\bot$ or $\top$. Let $N, M \geq 1$, let $S_0$ be a set of naturals each member $\ell$ of which either divides $\Delta_W$ (that is, fails `IsGoodPrimeFor`), or divides $M$, or equals $p$, and let $\kappa$ be a field of characteristic $p$. Assume [`HeckeEis.IsEigensystemH1`](def/Gamma0CoeffCohomologyEigen.html#L72) for level $N$, the trivial representation $1$ of $\Gamma_0(N)$ on $\kappa$, the constant family of coefficient maps equal to the identity, the set $S_0$ and the system $\ell \mapsto a_\ell(W) \bmod p$, where $a_\ell(W) = \#\mathbb{F}_\ell + 1 - \#(W \bmod \ell)$: there is a nonzero class $x$ in the cohomology `coeffH1` of that representation such that for every prime $\ell \nmid N$ with $\ell \notin S_0$ some $\kappa$-linear endomorphism $T$ of `coeffH1` satisfying `IsCoeffHeckeOnH1` for $N$, $\ell$ and the identity coefficient map has $Tx = a_\ell(W) \cdot x$. The conclusion produces an additive homomorphism $\varphi$ from [`CohCarrier.GammaH N ⊥`](def/CohCarrier_Level.html#L133), the subgroup of $\Gamma_0(N)$ of matrices with lower-right entry $\equiv 1 \bmod N$, to $\kappa$, such that: $\varphi \neq 0$; $\varphi$ lies in [`ModularCurve.Period.parabolicHoms`](def/ModularCurve_PeriodMap.html#L62), i.e. vanishes on the elements singled out by the predicate `IsParabolicHom`; $\varphi \circ (\gamma \mapsto \sigma\gamma\sigma^{-1}) = \varphi$ for every $\sigma \in \Gamma_0(N)$, so $\varphi$ is fixed by the raw diamond action of $\Gamma_0(N)$; and [`CohCarrier.heckeT N ⊥ ℓ κ`](def/CohCarrier_Level.html#L250) sends $\varphi$ to $a_\ell(W) \cdot \varphi$ for every prime $\ell$ with $\ell \nmid \Delta_W$, $\ell \nmid M$, $\ell \nmid N$ and $\ell \neq p$.
--
--   This is the passage from an eigensystem occurring in the cohomology of $\Gamma_0(N)$ with trivial $\kappa$-coefficients to a genuine eigenclass at level $\Gamma_1(N)$: restriction along $\Gamma_1(N) \leq \Gamma_0(N)$ yields a class that is nonzero, parabolic and diamond-invariant, the two exclusions using irreducibility of the mod $p$ representation of $W$ to rule out a class factoring through $(\mathbb{Z}/N)^\times$ with Eisenstein eigenvalues $1+\ell$. It is used by [`WeierstrassCurve.exists_H1_parabolic_not_dvd_heckeT_congr_apOfModel_of_isEigensystemH1_one`](thm.html#WeierstrassCurve.exists_H1_parabolic_not_dvd_heckeT_congr_apOfModel_of_isEigensystemH1_one) in the construction of the mod $p$ modular form attached to $W$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_H1_bot_ne_zero_parabolic_diamondRaw_eq_heckeT_eq_smul_of_isEigensystemH1_one.lean

import Mathlib
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup

theorem WeierstrassCurve.exists_H1_bot_ne_zero_parabolic_diamondRaw_eq_heckeT_eq_smul_of_isEigensystemH1_one
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hirr : W.ModRepIsIrreducible p)
    (N : ℕ) [NeZero N] (M : ℕ) [NeZero M] (S₀ : Set ℕ)
    (hS₀ : ∀ ℓ ∈ S₀, ¬ W.IsGoodPrimeFor ℓ ∨ ℓ ∣ M ∨ ℓ = p)
    (κ : Type) [Field κ] [CharP κ p]
    (hocc : HeckeEis.IsEigensystemH1 N (1 : Representation κ (Gamma0 N) κ) (fun _ => LinearMap.id) S₀
      (fun ℓ => ((W.apOfModel ℓ : ℤ) : κ))) :
    ∃ φ : CohCarrier.H1 N ⊥ κ, φ ≠ 0 ∧
      φ ∈ ModularCurve.Period.parabolicHoms κ (CohCarrier.GammaH N ⊥) κ ∧
      (∀ σ : Gamma0 N, CohCarrier.diamondRaw N ⊥ κ σ φ = φ) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ M → ¬ ℓ ∣ N → ℓ ≠ p →
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        CohCarrier.heckeT N ⊥ ℓ κ φ = ((W.apOfModel ℓ : ℤ) : κ) • φ) := by sorry
