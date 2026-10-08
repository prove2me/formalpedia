-- Prove2me | Theorems.Thm_UncoupledDyn_Finite_jordan_unique_nash
-- name    : UncoupledDyn.Finite.jordan_unique_nash
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T01:08:33.807166+00:00
-- url     : https://prove2.me/theorems/8b067a4e-fd5a-43f1-af2c-62f4416b497e
-- title:
--   §III, p. 1833 and fn. 14 — every game of 𝒰₀ has the unique Nash equilibrium x̄ⁱ(Γ) = a^{i−1}/(a^{i−1}+1)
-- statement:
--   Let $a=(a^1,a^2,a^3)$ with $a^i>0$ for every $i$, and let $\Gamma_a$ be the game of Jordan's family with parameters $a$ (player $i$ gets $a^i$ for playing $0$ against the next player's $1$, gets $1$ for playing $1$ against the next player's $0$, and $0$ otherwise). Then $\Gamma_a$ has exactly one Nash equilibrium in mixed strategies, namely
--   $$\bar x^i(\Gamma_a)=\frac{a^{i-1}}{a^{i-1}+1},\qquad i=1,2,3,$$
--   with indices taken modulo 3 (so $\bar x^1=a^3/(a^3+1)$). In particular, Jordan's game $\Gamma_0$ ($a^i=1$ for all $i$) has the unique Nash equilibrium $\bar x_0=(1/2,1/2,1/2)$.
--
--   This is the single-Nash-equilibrium property of the family $\mathcal U_0$, on which the §III proof of Theorem 1 rests: it identifies the rest point of every Nash-convergent dynamic at every game of the family.
--
--   **Formalization Note.** The page takes all $a^i$ close to $1$ ("$1-\varepsilon<a^i<1+\varepsilon$ for some small $\varepsilon>0$"); the statement here assumes only $a^i>0$, which contains every such family with $\varepsilon\le 1$ and is all that fn. 14's argument uses. Players are 0-based, so the formula reads `x i = a (i - 1) / (a (i - 1) + 1)` with subtraction in `Fin 3` (wrapping $0\mapsto 2$).
-- source:
--   Hart and Mas-Colell, Uncoupled Dynamics Do Not Lead to Nash Equilibrium, Amer. Econ. Rev. 93(5) (2003), p. 1833, §III, display of x̄ⁱ(Γ) and fn. 14

import Mathlib
import Definitions.Def_FatkhullinPolyak_Discrete_Matrix
import Definitions.Def_UncoupledDyn_Finite_Setting

namespace UncoupledDyn.Finite

theorem jordan_unique_nash (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i) :
    (∀ x : Fin 3 → ℝ, IsNash (jordanGame a) x ↔ x = fun i => a (i - 1) / (a (i - 1) + 1)) ∧
    (∀ x : Fin 3 → ℝ, IsNash Gamma0 x ↔ x = fun _ => (1 / 2 : ℝ)) := by sorry

end UncoupledDyn.Finite
