-- Prove2me | Theorems.Thm_SONATA_Undir_theorem_3_9
-- name    : SONATA.Undir.theorem_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:17:42.378809+00:00
-- url     : https://prove2.me/theorems/10ee7c70-4314-4a0c-b071-5e36fd1340bf
-- title:
--   Theorem 3.9, p. 22 — there is ᾱ ∈ (0, 1] such that for every α < ᾱ, U(xᵢ^ν) converges to U* R-linearly
-- statement:
--   Consider Problem (P), $\min_{\mathbf x\in\mathcal K}U(\mathbf x)=\frac1m\sum_if_i(\mathbf x)+G(\mathbf x)$, under Assumptions A and B, and the SONATA algorithm (11a)–(11d) under Assumptions C and D, with the constants of (15) and (24), and let $\mathbf x^\star$ be an optimal solution with value $U^\star=U(\mathbf x^\star)$. Assume
--   $$\tilde\mu_{\rm mn}\ge D^\ell_{\rm mn}.$$
--   Then there is a step size $\bar\alpha\in(0,1]$ such that for every $\alpha\in(0,\bar\alpha)$, every run of SONATA with step size $\alpha$ and every agent $i$, the values $U(\mathbf x_i^\nu)$ converge to $U^\star$ R-linearly: there are $C\in\mathbb R$ and $z\in[0,1)$ with
--   $$|U(\mathbf x_i^\nu)-U^\star|\le C\,z^\nu\qquad\text{for all }\nu=0,1,\dots$$
--
--   This is the main result of §3: SONATA, with any surrogates satisfying Assumption C, converges linearly for composite, constrained problems in which only the average $F$ is strongly convex. The threshold $\bar\alpha$ depends only on the problem data (the functions, the surrogates, the network and the constants of A, C, (15)), not on the starting point or the run; $C$ and $z$ may depend on the run and on $\alpha$.
--
--   **Formalization Note.** The run is relational: $\hat{\mathbf x}_i^\nu$ is any minimizer of (11a), and $\mathbf x^\star$ is any minimizer of $U$ on $\mathcal K$; the theorem quantifies over all runs. The quantifier order is $\exists\bar\alpha\ \forall\alpha<\bar\alpha\ \forall\text{run}\ \forall i\ \exists C,z$. The constants $L_i$ of (1) do not appear; they exist under Assumption A.
-- source:
--   Sun, Daneshmand & Scutari, Distributed Optimization Based on Gradient-tracking Revisited, arXiv:1905.02637v2, p. 22, Theorem 3.9; proof pp. 22–23

import Mathlib
import Definitions.Def_SONATA_Undir_Network
import Definitions.Def_SONATA_Undir_Setting

namespace SONATA.Undir

theorem theorem_3_9
    {m d : ℕ} {K O : Set (E d)} {f : Fin m → E d → ℝ} {G : E d → ℝ} {μ L : ℝ}
    {ft : Fin m → E d → E d → ℝ} {μt Lt Dl Du : Fin m → ℝ} {Gr : SimpleGraph (Fin m)}
    {W : Matrix (Fin m) (Fin m) ℝ} {xstar : E d}
    (hS : Standing K O f G μ L ft μt Lt Dl Du Gr W xstar)
    (hcond : Dlmn Dl ≤ mutmn μt) :
    ∃ αbar : ℝ, 0 < αbar ∧ αbar ≤ 1 ∧ ∀ α : ℝ, 0 < α → α < αbar →
      ∀ x y xh : ℕ → Stack m d, IsRun K f G ft W α x y xh →
        ∀ i : Fin m, ∃ C z : ℝ, 0 ≤ z ∧ z < 1 ∧
          ∀ ν : ℕ, |Uobj f G (x ν i) - Uobj f G xstar| ≤ C * z ^ ν := by sorry

end SONATA.Undir
