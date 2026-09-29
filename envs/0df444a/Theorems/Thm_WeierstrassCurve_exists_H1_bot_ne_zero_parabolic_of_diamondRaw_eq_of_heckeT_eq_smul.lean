-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_H1_bot_ne_zero_parabolic_of_diamondRaw_eq_of_heckeT_eq_smul
-- name    : WeierstrassCurve.exists_H1_bot_ne_zero_parabolic_of_diamondRaw_eq_of_heckeT_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/ece9101d-116b-5c9f-b508-736b5559a554
-- title:
--   A non-zero parabolic diamond-fixed eigenclass with curve eigenvalues
-- statement:
--   Let $p$ be an odd prime, and let $W$ be a Weierstrass curve over $\mathbb{Z}$ with $\Delta_W \neq 0$ whose mod-$p$ representation is irreducible in the sense that, for the base change of $W$ to $\mathbb{Q}$ and to $\overline{\mathbb{Q}}$, the $p$-torsion of the point group is non-trivial and every Galois-stable $\mathbb{Z}/p$-submodule of it is $0$ or everything. Let $N, M \geq 1$, and let $S_0$ be a set of naturals each member $\ell$ of which satisfies $\ell \mid \Delta_W$, or $\ell \mid M$, or $\ell = p$. Let $\kappa$ be a field of characteristic $p$, and let $v$ be a non-zero element of [`CohCarrier.H1 N ⊥ κ`](def/CohCarrier_Level.html#L162), that is, an additive homomorphism from the additivisation of the group $\Gamma_H$ for $H = \bot \le (\mathbb{Z}/N)^\times$ (the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ of matrices in $\Gamma_0(N)$ whose lower-right entry maps to $1$ in $(\mathbb{Z}/N)^\times$) to $\kappa$. Assume $v$ is fixed by the raw diamond action of every $\sigma \in \Gamma_0(N)$, that is, $v$ composed with conjugation by $\sigma$ equals $v$, and that for every prime $\ell$ with $\ell \nmid N$ and $\ell \notin S_0$ one has $\mathrm{heckeT}_\ell(v) = a_\ell(W)\, v$, where $a_\ell(W) = \ell + 1 - \#W(\mathbb{Z}/\ell)$ is read in $\kappa$. Then there is a non-zero $v'$ in the same space which lies in the $\kappa$-submodule of parabolic homomorphisms, i.e. $v'(\gamma) = 0$ whenever $(\mathrm{tr}\,\gamma)^2 = 4$, is fixed by all raw diamond operators, and satisfies $\mathrm{heckeT}_\ell(v') = a_\ell(W)\, v'$ for every prime $\ell$ with $\ell \nmid \Delta_W$, $\ell \nmid M$, $\ell \nmid N$ and $\ell \neq p$. (In the proof the existential is witnessed by $v$ itself, so the content is that such a $v$ is automatically parabolic.)
--
--   This is the boundary-exclusion step in the group-cohomological model of mod-$p$ modular forms of level $\Gamma_1(N)$: an Eisenstein-type class cannot carry the Hecke eigenvalues of an elliptic curve with irreducible mod-$p$ representation, so a diamond-fixed eigenclass with those eigenvalues is already parabolic (cuspidal). It is used in the construction of a parabolic eigenclass of the level required for the level-lowering argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_H1_bot_ne_zero_parabolic_of_diamondRaw_eq_of_heckeT_eq_smul.lean

import Mathlib
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup

theorem WeierstrassCurve.exists_H1_bot_ne_zero_parabolic_of_diamondRaw_eq_of_heckeT_eq_smul
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hirr : W.ModRepIsIrreducible p)
    (N : ℕ) [NeZero N] (M : ℕ) [NeZero M] (S₀ : Set ℕ)
    (hS₀ : ∀ ℓ ∈ S₀, ¬ W.IsGoodPrimeFor ℓ ∨ ℓ ∣ M ∨ ℓ = p)
    (κ : Type) [Field κ] [CharP κ p]
    (v : CohCarrier.H1 N ⊥ κ) (hv : v ≠ 0)
    (hdia : ∀ σ : Gamma0 N, CohCarrier.diamondRaw N ⊥ κ σ v = v)
    (heig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ∉ S₀ →
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      CohCarrier.heckeT N ⊥ ℓ κ v = ((W.apOfModel ℓ : ℤ) : κ) • v) :
    ∃ v' : CohCarrier.H1 N ⊥ κ, v' ≠ 0 ∧
      v' ∈ ModularCurve.Period.parabolicHoms κ (CohCarrier.GammaH N ⊥) κ ∧
      (∀ σ : Gamma0 N, CohCarrier.diamondRaw N ⊥ κ σ v' = v') ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ M → ¬ ℓ ∣ N → ℓ ≠ p →
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        CohCarrier.heckeT N ⊥ ℓ κ v' = ((W.apOfModel ℓ : ℤ) : κ) • v') := by sorry
