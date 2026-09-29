-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_H1_parabolic_not_dvd_heckeT_congr_apOfModel_of_isEigensystemH1_one
-- name    : WeierstrassCurve.exists_H1_parabolic_not_dvd_heckeT_congr_apOfModel_of_isEigensystemH1_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/2be4d6a3-dc99-5694-b3cc-66d989cd42da
-- title:
--   Integral parabolic mod-p eigenclass attached to W at level N
-- statement:
--   Fix a prime $p$ with $p \neq 2$, a Weierstrass curve $W$ over $\mathbb{Z}$ with $\Delta_W \neq 0$ whose mod-$p$ representation is irreducible in the sense of `ModRepIsIrreducible` (the $p$-torsion of $W$ over an algebraic closure of $\mathbb{Q}$ is nontrivial and every Galois-stable $\mathbb{Z}/p$-submodule of it is $\bot$ or $\top$), integers $N \geq 4$ and $M \geq 1$ (both nonzero), and a set $S_0$ of naturals each member $\ell$ of which satisfies $\ell \mid \Delta_W$, or $\ell \mid M$, or $\ell = p$. Let $\kappa$ be a field of characteristic $p$ and assume [`HeckeEis.IsEigensystemH1`](def/Gamma0CoeffCohomologyEigen.html#L72) holds for the trivial representation of $\Gamma_0(N)$ on $\kappa$, with multiplier maps the identity, exceptional set $S_0$, and eigenvalues $\ell \mapsto a_\ell(W) \bmod p$, where $a_\ell(W) = \#\mathbb{F}_\ell + 1 - \#(W \bmod \ell)$: that is, there is a nonzero class $x$ in the coefficient $H^1$ such that for every prime $\ell \nmid N$ with $\ell \notin S_0$ some operator satisfying `IsCoeffHeckeOnH1` at $\ell$ scales $x$ by $a_\ell(W)$. The conclusion produces a homomorphism $\varphi_0$ from the additive group of $\Gamma_H(N,\bot)$ — the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ of matrices in $\Gamma_0(N)$ with lower-right entry trivial in $(\mathbb{Z}/N)^\times$ — to $\mathbb{Z}$ such that: $\varphi_0$ lies in `parabolicHoms`, i.e. it vanishes on the elements singled out by `IsParabolicHom`; $\varphi_0$ is not $p$ times another such homomorphism; for every $\sigma \in \Gamma_0(N)$ the difference $\mathrm{diamondRaw}(\sigma)\varphi_0 - \varphi_0$ (precomposition with conjugation by $\sigma$, minus $\varphi_0$) is divisible by $p$; and for every prime $\ell$ with $\ell \nmid \Delta_W$, $\ell \nmid M$, $\ell \nmid N$ and $\ell \neq p$, the difference $\mathrm{heckeT}_\ell \varphi_0 - a_\ell(W)\varphi_0$ is divisible by $p$, where $\mathrm{heckeT}_\ell$ is the transfer-type Hecke operator built from `conjL`.
--
--   This is the integral lifting step of the Frey-curve modularity argument: an eigensystem occurring in $H^1$ with coefficients in characteristic $p$ is realised by an integral parabolic class on $\Gamma_1(N)$ that is primitive at $p$ and satisfies the expected Hecke and diamond congruences. It feeds the descent of the level to a divisor of $N$ in [`WeierstrassCurve.exists_H1_parabolic_not_dvd_diamondRaw_heckeT_congr_apOfModel_level_div_of_forall_linearMap_psCarrier_eq_zero`](thm.html#WeierstrassCurve.exists_H1_parabolic_not_dvd_diamondRaw_heckeT_congr_apOfModel_level_div_of_forall_linearMap_psCarrier_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_H1_parabolic_not_dvd_heckeT_congr_apOfModel_of_isEigensystemH1_one.lean

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

theorem WeierstrassCurve.exists_H1_parabolic_not_dvd_heckeT_congr_apOfModel_of_isEigensystemH1_one
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hirr : W.ModRepIsIrreducible p)
    (N : ℕ) [NeZero N] (hN : 4 ≤ N) (M : ℕ) [NeZero M] (S₀ : Set ℕ)
    (hS₀ : ∀ ℓ ∈ S₀, ¬ W.IsGoodPrimeFor ℓ ∨ ℓ ∣ M ∨ ℓ = p)
    (κ : Type) [Field κ] [CharP κ p]
    (hocc : HeckeEis.IsEigensystemH1 N (1 : Representation κ (Gamma0 N) κ) (fun _ => LinearMap.id) S₀
      (fun ℓ => ((W.apOfModel ℓ : ℤ) : κ))) :
    ∃ φ₀ : CohCarrier.H1 N ⊥ ℤ,
      φ₀ ∈ ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH N ⊥) ℤ ∧
      (¬ ∃ ψ : CohCarrier.H1 N ⊥ ℤ, φ₀ = (p : ℤ) • ψ) ∧
      (∀ σ : Gamma0 N, ∃ ψ : CohCarrier.H1 N ⊥ ℤ, CohCarrier.diamondRaw N ⊥ ℤ σ φ₀ - φ₀ = (p : ℤ) • ψ) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ M → ¬ ℓ ∣ N → ℓ ≠ p →
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        ∃ ψ : CohCarrier.H1 N ⊥ ℤ, CohCarrier.heckeT N ⊥ ℓ ℤ φ₀ - (W.apOfModel ℓ) • φ₀ = (p : ℤ) • ψ) := by sorry
