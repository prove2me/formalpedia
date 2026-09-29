-- Prove2me | Theorems.Thm_StochasticProg_LShaped_thm1_feasibility_via_componentwise_min
-- name    : StochasticProg.LShaped.thm1_feasibility_via_componentwise_min
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T20:06:17.205984+00:00
-- url     : https://prove2.me/theorems/89f5f041-9c9b-4b36-9f15-e964871a7002
-- title:
--   Chapter 5, Theorem 1 — feasibility test via the componentwise minimum of h
-- statement:
--   This is Chapter 5, Theorem 1 (p. 194) of Birge & Louveaux, *Introduction to Stochastic
--   Programming*: a shortcut feasibility test for the case where a single linear system suffices
--   to certify $x\in K_2$, avoiding Step 2's $K$ separate LP solves.
--
--   Let $I$ be a two-stage recourse instance (fixed recourse matrix $W$, $K$ scenarios of
--   $(q,h,T)$) in which the technology matrix $T$ is the same deterministic matrix $T_0$ across
--   every scenario (as assumed on p. 193, just before the statement), and suppose $W$ is such that
--   every nonnegative vector lies in $\mathrm{pos}\,W$ (`posW`, the nonnegative column span of
--   $W$). Let $a_i=\min_{k=1,\dots,K}h_{ik}$ be the componentwise minimum, over the $K$
--   realizations, of the right-hand-side vector $h$, and suppose some realization $h^\ell$ attains
--   it exactly, $a=h^\ell$.
--
--   Then, for any first-stage decision $x$,
--   $$
--   x\in K_2 \iff \exists\, y\ge 0,\ Wy = a - T_0x,
--   $$
--   i.e. second-stage feasibility at *every* scenario is equivalent to the feasibility of a
--   single linear system built from the componentwise-worst right-hand side $a$.
--
--   **Formalization Note** `posW inst t` is the companion `Bases` bundle's predicate for
--   $t\in\mathrm{pos}\,W$. The componentwise minimum $a$ is supplied as a hypothesis
--   (`ha : ∀ i, a i = sInf {v | ∃ k, v = inst.h k i}`) rather than computed by a `Finset.min'`
--   over `Fin K`, since `sInf` over a finite nonempty set of reals already equals the ordinary
--   minimum and keeps the statement close to the book's own "$a_i=\min_k\{h_{ik}\}$" notation.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, p. 194, Chapter 5, Theorem 1

import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance
import Definitions.Def_StochasticProg_LShaped_Bases

namespace StochasticProg.LShaped

open StochasticProg.Recourse

variable {n1 n2 m1 m2 K : ℕ}

/-- Chapter 5, Theorem 1 (p. 194): "Assume that `W` is such that `t ∈ pos W` for all
`t ≥ 0`. Define `a_i = min_{k=1,...,K}{h_ik}` to be the componentwise minimum of `h`. Also
assume there exists one realization `hℓ, ℓ ∈ {1,...,K}` s.t. `a = hℓ`. Then, `x ∈ K2` if
and only if `Wy = a − Tx, y ≥ 0` is feasible." (`T` deterministic, as assumed on p. 193
just before the statement.) -/
theorem thm1_feasibility_via_componentwise_min
    (inst : Instance n1 n2 m1 m2 K) (hK : 0 < K)
    (T0 : Matrix (Fin m2) (Fin n1) ℝ) (hT : ∀ k, inst.T k = T0)
    (hWpos : ∀ t : Fin m2 → ℝ, (∀ i, 0 ≤ t i) → posW inst t)
    (a : Fin m2 → ℝ) (ha : ∀ i, a i = sInf {v : ℝ | ∃ k : Fin K, v = inst.h k i})
    (ℓ : Fin K) (haℓ : a = inst.h ℓ) (x : Fin n1 → ℝ) :
    x ∈ K2 inst ↔
      ∃ y : Fin n2 → ℝ, (∀ i, 0 ≤ y i) ∧ Matrix.mulVec inst.W y = a - Matrix.mulVec T0 x := by sorry

end StochasticProg.LShaped
