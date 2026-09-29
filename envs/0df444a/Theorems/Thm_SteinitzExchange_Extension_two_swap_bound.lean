-- Prove2me | Theorems.Thm_SteinitzExchange_Extension_two_swap_bound
-- name    : SteinitzExchange.Extension.two_swap_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:41:43.086966+00:00
-- url     : https://prove2.me/theorems/24c489f6-c513-42ac-b7b9-eee3ef68e8d9
-- title:
--   Lemma 3.2 — the two-swap bound under (EXC$_{\mathrm{loc}}$)
-- statement:
--   Let $B\subseteq\mathbb Z^V$ be a finite integral base set and let $\omega:B\to\mathbb R$ satisfy the local exchange property (EXC$_{\mathrm{loc}}$). Let $x\in B$ and $u_0,u_1,v_0,v_1\in V$ with $\{u_0,u_1\}\cap\{v_0,v_1\}=\emptyset$ be such that
--   $$y:=x-\chi_{u_0}-\chi_{u_1}+\chi_{v_0}+\chi_{v_1}\in B,$$
--   and let $p:V\to\mathbb R$. Write $\omega_p=\omega[p]$ and $\pi_{ij}=\omega_p(x-\chi_{u_i}+\chi_{v_j})-\omega_p(x)$, with $\pi_{ij}=-\infty$ when $x-\chi_{u_i}+\chi_{v_j}\notin B$. Then
--   $$\omega_p(y)-\omega_p(x)\le\max(\pi_{00}+\pi_{11},\ \pi_{01}+\pi_{10}).\qquad(3.3)$$
--   The cases $u_0=u_1$ or $v_0=v_1$ are allowed.
--
--   This bound is the local step behind Theorem 3.1 (local exchange implies global exchange).
--
--   **Formalization Note.** With the $-\infty$ convention, (3.3) says exactly: either $x-\chi_{u_0}+\chi_{v_0}$ and $x-\chi_{u_1}+\chi_{v_1}$ both lie in $B$ and $\omega_p(y)-\omega_p(x)\le\pi_{00}+\pi_{11}$, or $x-\chi_{u_0}+\chi_{v_1}$ and $x-\chi_{u_1}+\chi_{v_0}$ both lie in $B$ and $\omega_p(y)-\omega_p(x)\le\pi_{01}+\pi_{10}$. The Lean statement is this disjunction. The hypothesis (EXC$_{\mathrm{loc}}$) is on $\omega$, not on $\omega_p$.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 282, Lemma 3.2, Eq. (3.3)

import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Extension_Exchange

namespace SteinitzExchange.Extension

/-- Murota 1996, p. 282, Lemma 3.2. With the paper's convention `ω_p(x, u, v) = −∞` when
`x − χ_u + χ_v ∉ B`, the bound `ω_p(y) − ω_p(x) ≤ max(π₀₀ + π₁₁, π₀₁ + π₁₀)` says: for one of the
two pairings, both exchanged points lie in `B` and the bound holds with that pairing. -/
theorem two_swap_bound {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ)
    (hloc : SatisfiesEXCLoc B ω) (x : V → ℤ) (hx : x ∈ B) (u₀ u₁ v₀ v₁ : V)
    (hy : x - chi u₀ - chi u₁ + chi v₀ + chi v₁ ∈ B)
    (h00 : u₀ ≠ v₀) (h01 : u₀ ≠ v₁) (h10 : u₁ ≠ v₀) (h11 : u₁ ≠ v₁) (p : V → ℝ) :
    let y := x - chi u₀ - chi u₁ + chi v₀ + chi v₁
    let π : V → V → ℝ := fun u v => perturb ω p (x - chi u + chi v) - perturb ω p x
    (x - chi u₀ + chi v₀ ∈ B ∧ x - chi u₁ + chi v₁ ∈ B ∧
        perturb ω p y - perturb ω p x ≤ π u₀ v₀ + π u₁ v₁) ∨
      (x - chi u₀ + chi v₁ ∈ B ∧ x - chi u₁ + chi v₀ ∈ B ∧
        perturb ω p y - perturb ω p x ≤ π u₀ v₁ + π u₁ v₀) := by sorry

end SteinitzExchange.Extension
