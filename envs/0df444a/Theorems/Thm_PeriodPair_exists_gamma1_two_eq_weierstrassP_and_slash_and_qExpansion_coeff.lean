-- Prove2me | Theorems.Thm_PeriodPair_exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff
-- name    : PeriodPair.exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/d77e5327-b7d7-5e48-8a05-e2e578215970
-- title:
--   Division values of wp as weight-two forms on Γ₁(M)
-- statement:
--   For every natural number $M \neq 0$ there exists a family $W : \mathbb{Z}/M \to$ (modular forms of weight $2$ for the congruence subgroup $\Gamma_1(M)$, regarded as a subgroup of $\mathrm{GL}_2(\mathbb{R})$) with three properties. First, for every assignment $L$ of a period pair to each point $\tau$ of the upper half-plane such that $(L\,\tau).\omega_1 = \tau$ and $(L\,\tau).\omega_2 = 1$, and for all $t \in \mathbb{Z}/M$ and all $\tau$, one has $W_t(\tau) = 12\,(2\pi i)^{-2}\,\wp_{L\,\tau}(\tilde t/M)$, where $\tilde t \in \{0,\dots,M-1\}$ is the canonical representative of $t$ and $\wp_{L\,\tau}$ is the Weierstrass function attached to the period pair. Second, for all $t \in \mathbb{Z}/M$ and all $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma_0(M)$, the weight-two slash satisfies $W_t \mid_2 \gamma = W_{t\,d}$ as functions on the upper half-plane, where $d$ is the reduction mod $M$ of the $(1,1)$ entry (in zero-based indexing: the lower right entry) of $\gamma$. Third, for every $t \neq 0$ and every $n \in \mathbb{N}$, the $n$-th coefficient of the $q$-expansion of $W_t$ of width $1$ equals $1 + 12\,\zeta^{\tilde t}/(1-\zeta^{\tilde t})^2$ if $n = 0$, and otherwise $12\big(\sum_{d \mid n} d\,(\zeta^{\tilde t d} + \zeta^{-\tilde t d}) - 2\sum_{d \mid n} d\big)$, where $\zeta = e^{2\pi i/M}$.
--
--   These are, up to the normalising factor $12/(2\pi i)^2$, the weight-two Eisenstein series obtained by evaluating $\wp$ at the $M$-division points $t/M$ of the lattice $\mathbb{Z}\tau + \mathbb{Z}$; the displayed $q$-expansion is the Tate-curve series $X(\zeta^{\tilde t}, q)$ shifted by $1$. The statement is the source of the weight-two forms used in the constructions of modular forms on $\Gamma_H$ and at auxiliary level, where the $\Gamma_0(M)$-permutation rule supplies the action of the diamond operators on the family.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PeriodPair_exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm Real Matrix

theorem PeriodPair.exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff
    (M : ℕ) [NeZero M] :
    ∃ W : ZMod M → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) 2,
      (∀ (L : UpperHalfPlane → PeriodPair),
        (∀ τ : UpperHalfPlane, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1) →
        ∀ (t : ZMod M) (τ : UpperHalfPlane),
          W t τ = 12 * ((2 * π * Complex.I) ^ 2)⁻¹ * (L τ).weierstrassP ((t.val : ℂ) / M)) ∧
      (∀ (t : ZMod M) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M →
        (⇑(W t) : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] γ = ⇑(W (t * ((γ 1 1 : ℤ) : ZMod M)))) ∧
      ∀ t : ZMod M, t ≠ 0 → ∀ n : ℕ,
        (UpperHalfPlane.qExpansion 1 (W t)).coeff n =
          if n = 0 then
            1 + 12 * Complex.exp (2 * π * Complex.I / M) ^ t.val /
              (1 - Complex.exp (2 * π * Complex.I / M) ^ t.val) ^ 2
          else
            12 * ((∑ d ∈ n.divisors, (d : ℂ) *
                (Complex.exp (2 * π * Complex.I / M) ^ (t.val * d) +
                  (Complex.exp (2 * π * Complex.I / M))⁻¹ ^ (t.val * d))) -
              2 * ∑ d ∈ n.divisors, (d : ℂ)) := by sorry
