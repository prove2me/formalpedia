-- Prove2me | Theorems.Thm_PeriodPair_weierstrassP_torsion_modularForm_slash_tendsto_atImInfty
-- name    : PeriodPair.weierstrassP_torsion_modularForm_slash_tendsto_atImInfty
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/d8b4ee7b-8941-5ab6-938c-425427abbfb9
-- title:
--   Division values of wp are weight-two forms for Γ(N)
-- statement:
--   Let $L$ assign to each point $\tau$ of the upper half-plane a period pair $L(\tau)$, and assume $hL$: for every $\tau$ the two periods of $L(\tau)$ are $\omega_1=\tau$ and $\omega_2=1$, so that $L(\tau)$ presents the lattice $\mathbb Z\tau+\mathbb Z$. Let $N$ be a nonzero natural number and $a\in(\mathbb Z/N\mathbb Z)^2$ a row vector indexed by `Fin 2`. Write, for $b\in(\mathbb Z/N\mathbb Z)^2$, $W_b(\tau)=\wp_{L(\tau)}\bigl((\tilde b_0\tau+\tilde b_1)/N\bigr)$, where $\tilde b_i\in\{0,\dots,N-1\}$ is the canonical representative of $b_i$ and $\wp$ is the Weierstrass function of the period pair. The conclusion is a conjunction of three assertions. First, $W_a$ is (the function underlying) a modular form of weight $2$ for the principal congruence subgroup $\Gamma(N)$, i.e. there exists $F$ of type `ModularForm (CongruenceSubgroup.Gamma N) 2` whose coercion to a function equals $W_a$. Second, for every $\gamma\in\mathrm{SL}_2(\mathbb Z)$ the weight-$2$ slash action satisfies $W_a\mid_2\gamma=W_{a\,\bar\gamma}$, where $a\,\bar\gamma$ is the row vector $a$ multiplied on the right by the reduction of $\gamma$ modulo $N$. Third, if $a\neq0$ then $W_a(\tau)$ tends, as $\operatorname{Im}\tau\to\infty$, to $-\pi^2/3+\pi^2/\sin^2(\pi\tilde a_1/N)$ when $a_0=0$, and to $-\pi^2/3$ when $a_0\neq0$. The first two assertions are stated for every $a$, the third only for $a\neq0$.
--
--   The functions $W_a$ are the classical weight-two Eisenstein series of level $N$ realised as division values of the Weierstrass $\wp$-function; the non-modular corrections of the naive weight-two Eisenstein sums cancel, so these division values are genuine modular forms, and their values at the cusp $i\infty$ are computed from Lipschitz's formula. The result is used in the construction of weight-two forms of level $N$ with prescribed behaviour under the slash action and in the comparison of $q$-expansion coefficients with substitutions into the Tate curve parameter.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PeriodPair_weierstrassP_torsion_modularForm_slash_tendsto_atImInfty.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm Topology Real Matrix

theorem PeriodPair.weierstrassP_torsion_modularForm_slash_tendsto_atImInfty
    (L : UpperHalfPlane → PeriodPair) (hL : ∀ τ : UpperHalfPlane, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (N : ℕ) [NeZero N] (a : Fin 2 → ZMod N) :
    let W : (Fin 2 → ZMod N) → UpperHalfPlane → ℂ :=
      fun b τ => (L τ).weierstrassP ((((b 0).val : ℂ) * (τ : ℂ) + (b 1).val) / N)
    (∃ F : ModularForm (CongruenceSubgroup.Gamma N) 2, ⇑F = W a) ∧
    (∀ γ : SL(2, ℤ), W a ∣[(2 : ℤ)] γ = W (a ᵥ* ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)))) ∧
    (a ≠ 0 → Filter.Tendsto (W a) UpperHalfPlane.atImInfty
      (𝓝 (-((π : ℂ) ^ 2 / 3) + if a 0 = 0 then (π : ℂ) ^ 2 / Complex.sin (π * (a 1).val / N) ^ 2 else 0))) := by sorry
