-- Prove2me | Theorems.Thm_StochasticProg_LShaped_thm1_feasibility_via_componentwise_min_v2
-- name    : StochasticProg.LShaped.thm1_feasibility_via_componentwise_min_v2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T03:40:26.577443+00:00
-- url     : https://prove2.me/theorems/2e79cad3-0726-491f-a2b6-23b936d1ea17
-- title:
--   Chapter 5, Theorem 1 — feasibility test via the componentwise minimum of h (corrected)
-- statement:
--   Corrected version (v2) of Chapter 5, Theorem 1 (p. 194) of Birge & Louveaux, *Introduction to Stochastic Programming*: a single linear system decides second-stage feasibility.
--
--   Let $I$ be a two-stage recourse instance in which every realization has positive probability, $p_k>0$ (§5.1, p. 182), and the technology matrix is the same deterministic $T_0$ in every scenario (p. 193). Suppose every nonnegative vector lies in $\mathrm{pos}\,W$, let $a_i=\min_k h_{ik}$ be the componentwise minimum of the right-hand sides, and suppose some realization attains it, $a=h^\ell$. Then for every first-stage $x$,
--   $$x\in K_2 \iff \exists\, y\ge 0,\ Wy=a-T_0x .$$
--
--   This replaces `StochasticProg.LShaped.thm1_feasibility_via_componentwise_min`, which was disproved by a zero-probability realization: with $p_\ell=0$ the set $K_2$ ignores scenario $\ell$ (in the definitions $0\cdot\top=0$), so the right-hand side can fail while $x\in K_2$.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, Ch. 5 §5.1 Theorem 1, printed p. 194; deterministic T assumed on p. 193; realizations p. 182

import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance
import Definitions.Def_StochasticProg_LShaped_Bases
import Definitions.Def_StochasticProg_LShaped_Algorithm

namespace StochasticProg.LShaped

open StochasticProg.Recourse

variable {n1 n2 m1 m2 K : ℕ}

/-- Chapter 5, Theorem 1 (p. 194): "Assume that `W` is such that `t ∈ pos W` for all
`t ≥ 0`. Define `a_i = min_{k=1,...,K}{h_ik}` to be the componentwise minimum of `h`. Also
assume there exists one realization `hℓ, ℓ ∈ {1,...,K}` s.t. `a = hℓ`. Then, `x ∈ K2` if
and only if `Wy = a − Tx, y ≥ 0` is feasible." (`T` deterministic, as assumed on p. 193
just before the statement.)

v2 (2026-10-05): the published statement was disproved by a zero-probability realization (with `p_ℓ = 0`, `K2` ignores scenario ℓ since `0 * ⊤ = 0`). This version requires every realization to have positive probability (`hp_pos`), as §5.1 assumes (k indexes the possible realizations). -/
theorem thm1_feasibility_via_componentwise_min_v2
    (inst : Instance n1 n2 m1 m2 K) (hK : 0 < K) (hp_pos : ∀ k, 0 < inst.p k)
    (T0 : Matrix (Fin m2) (Fin n1) ℝ) (hT : ∀ k, inst.T k = T0)
    (hWpos : ∀ t : Fin m2 → ℝ, (∀ i, 0 ≤ t i) → posW inst t)
    (a : Fin m2 → ℝ) (ha : ∀ i, a i = sInf {v : ℝ | ∃ k : Fin K, v = inst.h k i})
    (ℓ : Fin K) (haℓ : a = inst.h ℓ) (x : Fin n1 → ℝ) :
    x ∈ K2 inst ↔
      ∃ y : Fin n2 → ℝ, (∀ i, 0 ≤ y i) ∧ Matrix.mulVec inst.W y = a - Matrix.mulVec T0 x := by
  sorry

end StochasticProg.LShaped
