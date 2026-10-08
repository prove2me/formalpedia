-- Prove2me | Theorems.Thm_PhiDivRobust_Counterpart_robust_counterpart_iff
-- name    : PhiDivRobust.Counterpart.robust_counterpart_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T18:52:01.345314+00:00
-- url     : https://prove2.me/theorems/258c197c-ed0f-42a1-98a0-6ce817db9f34
-- title:
--   Theorem 1 — robust counterpart of a linear constraint under φ-divergence uncertainty (for q > 0)
-- statement:
--   Let $\phi$ be a φ-divergence function with conjugate $\phi^*(s)=\sup_{t\ge0}\{st-\phi(t)\}$. Let $a\in\mathbb R^n$, $B\in\mathbb R^{n\times m}$, $\beta\in\mathbb R$, $C\in\mathbb R^{k\times m}$, $d\in\mathbb R^k$, let $q\in\mathbb R^m$ with $q_i>0$ for all $i$, and let $\rho>0$. Consider the uncertainty region
--
--   $$U=\{p\in\mathbb R^m\mid p\ge0,\ Cp\le d,\ I_\phi(p,q)\le\rho\},\qquad I_\phi(p,q)=\sum_{i=1}^m q_i\phi(p_i/q_i),$$
--
--   and assume $q\in U$. Write $b_i$ and $c_i$ for the $i$-th columns of $B$ and $C$. Then a vector $x\in\mathbb R^n$ satisfies the robust constraint
--
--   $$(a+Bp)^\top x\le\beta\qquad\forall p\in U \tag{11}$$
--
--   if and only if there exist $\eta\in\mathbb R^k$ and $\lambda\in\mathbb R$ such that
--
--   $$a^\top x + d^\top\eta + \rho\lambda + \lambda\sum_i q_i\,\phi^*\!\left(\frac{b_i^\top x - c_i^\top\eta}{\lambda}\right)\le\beta,\qquad \eta\ge0,\ \lambda\ge0, \tag{13}$$
--
--   with the convention $0\phi^*(s/0):=0$ if $s\le0$ and $0\phi^*(s/0):=+\infty$ if $s>0$.
--
--   The theorem replaces the semi-infinite constraint (11) by a finite convex system in $(x,\lambda,\eta)$, which is tractable whenever $\phi^*$ is (Table 4 of the paper).
--
--   **Formalization Note** (i) The paper prints the standing assumption $q\ge0$; with some $q_i=0$ the theorem is false (the change of variables in (15) fails), so it is stated for $q>0$. A counterexample to the printed form: $m=k=2$, $n=1$, $\phi(t)=|t-1|$, $q=(1,0)$, both columns of $C$ equal to $(1,-1)^\top$, $d=(1,-1)$, $a=0$, $B=(0\ \ 1)$, $x=1$, $\rho=1$, $\beta=0$; then $p=(1/2,1/2)\in U$ violates (11), yet $\eta=0$, $\lambda=0$ satisfy (13). (ii) The left side of (13) is computed in `EReal`: $\lambda\sum_i q_i\phi^*(\cdot/\lambda)$ is read as $\sum_i q_i\cdot\big(\lambda\phi^*(\cdot/\lambda)\big)$ with the $\lambda=0$ convention applied term by term. (iii) With $q>0$ the hypothesis $q\in U$ amounts to $Cq\le d$; it is kept in the paper's form.
-- source:
--   Ben-Tal, den Hertog, De Waegenaere, Melenberg, Rennen, Robust Solutions of Optimization Problems Affected by Uncertain Probabilities, Management Sci. 59(2), 2013, p. 347, Theorem 1 and Eq. (13)

import Mathlib
import Definitions.Def_PhiDivRobust_Counterpart_IsPhiDivergenceFunction
import Definitions.Def_PhiDivRobust_Counterpart_uncertaintySet
import Definitions.Def_PhiDivRobust_Counterpart_perspConj
open Matrix

namespace PhiDivRobust.Counterpart

/-- Theorem 1 of Ben-Tal et al. 2013 (p. 347), stated for `q > 0` (the printed `q ≥ 0` is false):
`x` satisfies `(a + Bp)ᵀx ≤ β` for all `p` in the φ-divergence region (12), where `q ∈ U`, iff there
are `η ∈ ℝᵏ`, `λ ∈ ℝ` with `η ≥ 0`, `λ ≥ 0` and
`aᵀx + dᵀη + ρλ + ∑ᵢ qᵢ · λφ*((bᵢᵀx − cᵢᵀη)/λ) ≤ β` (13), with `0φ*(s/0) := 0` for `s ≤ 0` and
`+∞` for `s > 0`; `bᵢ`, `cᵢ` are the `i`-th columns of `B` and `C`. -/
theorem robust_counterpart_iff {n m k : ℕ} (φ : ℝ → EReal) (hφ : IsPhiDivergenceFunction φ)
    (a : Fin n → ℝ) (B : Matrix (Fin n) (Fin m) ℝ) (β : ℝ) (C : Matrix (Fin k) (Fin m) ℝ)
    (d : Fin k → ℝ) (q : Fin m → ℝ) (ρ : ℝ) (hq : ∀ i, 0 < q i) (hρ : 0 < ρ)
    (hqU : q ∈ uncertaintySet φ C d q ρ) (x : Fin n → ℝ) :
    (∀ p ∈ uncertaintySet φ C d q ρ, (a + B *ᵥ p) ⬝ᵥ x ≤ β) ↔
      ∃ η : Fin k → ℝ, ∃ lam : ℝ, 0 ≤ η ∧ 0 ≤ lam ∧
        ((a ⬝ᵥ x + d ⬝ᵥ η + ρ * lam : ℝ) : EReal) +
          ∑ i, (q i : EReal) *
            perspConj φ lam ((fun j => B j i) ⬝ᵥ x - (fun j => C j i) ⬝ᵥ η) ≤ (β : EReal) := by sorry

end PhiDivRobust.Counterpart
