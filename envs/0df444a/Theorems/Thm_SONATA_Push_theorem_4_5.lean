-- Prove2me | Theorems.Thm_SONATA_Push_theorem_4_5
-- name    : SONATA.Push.theorem_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:13:59.206148+00:00
-- url     : https://prove2.me/theorems/cec268c2-a33f-468f-ab18-17d9224c7e12
-- title:
--   Theorem 4.5, p. 31 — there is ᾱ ∈ (0,1] such that for every α < ᾱ, U(x_i^ν) converges to U* R-linearly
-- statement:
--   Consider Problem (P) under Assumptions A and B′, and SONATA (Algorithm 3) under Assumptions C and E, with constants $D^\ell_i\le D^u_i$ satisfying (15) and a solution $x^\star$ of (P). Suppose
--   $$\tilde\mu_{\rm mn}\ge D^\ell_{\rm mn}.$$
--   Then there is a step-size threshold $\bar\alpha\in(0,1]$, depending only on the problem data and the network, such that for every $\alpha\in(0,\bar\alpha)$, every run of Algorithm 3 with step size $\alpha$ and every agent $i$, the values $U(x_i^\nu)$ converge to $U^\star=U(x^\star)$ at an R-linear rate: there are constants $C$ and $z\in[0,1)$ with
--   $$|U(x_i^\nu)-U^\star|\le C\,z^\nu\qquad\text{for all }\nu=0,1,\dots$$
--
--   This is the main result for time-varying directed networks: linear convergence of distributed composite, constrained optimization with surrogates, with push-sum weights replacing a doubly stochastic mixing matrix.
--
--   **Formalization Note** The graph sequence, $B$, $c_\ell$ and the matrices $C^\nu$ are fixed before $\bar\alpha$; the starting point and the run come after $\alpha$. The constants $C$ and $z$ may depend on the run and on $\alpha$.
-- source:
--   Sun, Daneshmand & Scutari, Distributed Optimization Based on Gradient-tracking Revisited, arXiv:1905.02637v2, p. 31, Theorem 4.5; proof Supporting Material II, p. 49

import Mathlib
import Definitions.Def_SONATA_Push_Network

namespace SONATA.Push

/-- Theorem 4.5 (p. 31). Under Assumptions A, B′, C, (15) and E, with `μ̃_mn ≥ D^ℓ_mn`, there is
`ᾱ ∈ (0, 1]` such that for every step size `α ∈ (0, ᾱ)`, every run of Algorithm 3 and every agent `i`,
`U(x_i^ν)` converges to `U⋆` R-linearly. -/
theorem theorem_4_5
    {m d : ℕ} (K O : Set (SONATA.Undir.E d)) (f : Fin m → SONATA.Undir.E d → ℝ) (G : SONATA.Undir.E d → ℝ) (μ L : ℝ)
    (ft : Fin m → SONATA.Undir.E d → SONATA.Undir.E d → ℝ) (μt Lt Dl Du : Fin m → ℝ) (xstar : SONATA.Undir.E d)
    (Edges : ℕ → Fin m → Fin m → Prop) (B : ℕ) (C : ℕ → Matrix (Fin m) (Fin m) ℝ) (cl : ℝ)
    (hP : ProblemHyp K O f G μ L ft μt Lt Dl Du xstar) (hN : NetworkHyp Edges B C cl)
    (hcond : SONATA.Undir.Dlmn Dl ≤ SONATA.Undir.mutmn μt) :
    ∃ αbar : ℝ, 0 < αbar ∧ αbar ≤ 1 ∧ ∀ α : ℝ, 0 < α → α < αbar →
      ∀ x y xh : ℕ → Fin m → SONATA.Undir.E d, ∀ φ : ℕ → Fin m → ℝ, IsRun K f G ft C α x y xh φ →
        ∀ i : Fin m, ∃ Cc z : ℝ, 0 ≤ z ∧ z < 1 ∧
          ∀ ν : ℕ, |U f G (x ν i) - U f G xstar| ≤ Cc * z ^ ν := by sorry

end SONATA.Push
