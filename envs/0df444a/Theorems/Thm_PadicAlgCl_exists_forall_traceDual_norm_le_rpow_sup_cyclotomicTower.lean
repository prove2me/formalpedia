-- Prove2me | Theorems.Thm_PadicAlgCl_exists_forall_traceDual_norm_le_rpow_sup_cyclotomicTower
-- name    : PadicAlgCl.exists_forall_traceDual_norm_le_rpow_sup_cyclotomicTower
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/63a3bb2c-0c0e-5f4e-ab8a-ef91430672a5
-- title:
--   Tate: different of MK(μ_{pⁿ})/K(μ_{pⁿ}) tends to one
-- statement:
--   Fix a prime $p$ and work inside a fixed algebraic closure $\overline{\mathbb{Q}}_p$ of $\mathbb{Q}_p$ (the type `PadicAlgCl p`), with its canonical absolute value $\|\cdot\|$. Let $K$ and $M$ be intermediate fields of $\overline{\mathbb{Q}}_p/\mathbb{Q}_p$, each finite-dimensional over $\mathbb{Q}_p$, and let $\varepsilon$ be a real number with $0 < \varepsilon$. For $n \in \mathbb{N}$ write $T_n =$ [`PadicAlgCl.cyclotomicTower p n`](def/PadicAlgCl_CyclotomicTower.html#L9) for the intermediate field obtained by adjoining to $\mathbb{Q}_p$ the set of all $\zeta \in \overline{\mathbb{Q}}_p$ with $\zeta^{p^n} = 1$, and set $F_n = K \sqcup T_n$ and $E_n = M \sqcup F_n$ (joins of intermediate fields), $E_n$ being regarded via `IntermediateField.extendScalars` along $F_n \le E_n$ as an extension of $F_n$. The assertion is that there exists $N \in \mathbb{N}$ such that for every $n \ge N$ and every $z \in E_n$, if for all $w \in E_n$ with $\|w\| \le 1$ one has $\|\mathrm{Tr}_{E_n/F_n}(zw)\| \le 1$ (the trace being taken in $F_n$ and measured in $\overline{\mathbb{Q}}_p$), then $\|z\| \le p^{\varepsilon}$.
--
--   This is the ramification-theoretic core of Tate's result that the cyclotomic tower is almost étale: the codifferent of $MK(\mu_{p^n})$ over $K(\mu_{p^n})$ is eventually contained in the ball of radius $p^{\varepsilon}$, equivalently the valuation of the different of these layers tends to $0$. It is used to produce elements of small norm with prescribed trace along the tower, in [`PadicAlgCl.exists_norm_le_one_and_trace_eq_of_norm_lt_one_sup_cyclotomicTower`](thm.html#PadicAlgCl.exists_norm_le_one_and_trace_eq_of_norm_lt_one_sup_cyclotomicTower).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicAlgCl_exists_forall_traceDual_norm_le_rpow_sup_cyclotomicTower.lean

import Mathlib
import Definitions.Def_PadicAlgCl_CyclotomicTower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PadicAlgCl.exists_forall_traceDual_norm_le_rpow_sup_cyclotomicTower
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (M : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] M]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ z : IntermediateField.extendScalars (F := K ⊔ PadicAlgCl.cyclotomicTower p n)
          (E := M ⊔ (K ⊔ PadicAlgCl.cyclotomicTower p n)) le_sup_right,
        (∀ w : IntermediateField.extendScalars (F := K ⊔ PadicAlgCl.cyclotomicTower p n)
            (E := M ⊔ (K ⊔ PadicAlgCl.cyclotomicTower p n)) le_sup_right,
          ‖(w : PadicAlgCl p)‖ ≤ 1 →
          ‖((Algebra.trace ↥(K ⊔ PadicAlgCl.cyclotomicTower p n)
              ↥(IntermediateField.extendScalars (F := K ⊔ PadicAlgCl.cyclotomicTower p n)
                (E := M ⊔ (K ⊔ PadicAlgCl.cyclotomicTower p n)) le_sup_right) (z * w) :
                ↥(K ⊔ PadicAlgCl.cyclotomicTower p n)) : PadicAlgCl p)‖ ≤ 1) →
        ‖(z : PadicAlgCl p)‖ ≤ (p : ℝ) ^ ε := by sorry
