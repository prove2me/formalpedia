-- Prove2me | Theorems.Thm_SimplicialIso_Cheeger_eq_4_2
-- name    : SimplicialIso.Cheeger.eq_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:21:12.181739+00:00
-- url     : https://prove2.me/theorems/da5f1076-cf25-4159-b7ad-4376c67d6d81
-- title:
--   (4.2), p. 12 — Rayleigh's principle: λ(X)⟨f,f⟩ ≤ ⟨Δ⁺f,f⟩ = ⟨∂*_d f,∂*_d f⟩ for every f ∈ Z_{d−1}
-- statement:
--   Let $X$ be a finite $d$-dimensional simplicial complex with a complete skeleton on $n\ge d+1$ vertices, $d\ge1$. Then the upper Laplacian $\Delta^+$ restricted to the $(d-1)$-cycles $Z_{d-1}$ has a least eigenvalue $\lambda(X)=\min\operatorname{Spec}(\Delta^+|_{Z_{d-1}})$ (Definition 2.1), and for every $f\in Z_{d-1}$
--   $$\lambda(X)\,\langle f,f\rangle\le\langle\Delta^+f,f\rangle=\langle\partial_d^*f,\partial_d^*f\rangle .$$
--   For $f\neq0$ this is (4.2): $\lambda(X)\le \langle\Delta^+ f,f\rangle/\langle f,f\rangle=\langle\partial_d^*f,\partial_d^*f\rangle/\langle f,f\rangle$. It reduces Theorem 1.2 to computing the Rayleigh quotient of the test form (4.1).
--
--   **Formalization Note.** The conclusion asserts that some $\mu$ is an eigenvalue of $\Delta^+$ on $Z_{d-1}$ (a nonzero cycle $f$ with $\Delta^+f=\mu f$), that $\mu$ is at most every such eigenvalue, and the inequality multiplied out by $\langle f,f\rangle$, so there is no division. $n\ge d+1$ makes $Z_{d-1}\neq0$ (the paper presupposes it: $h(X)$ is a minimum over partitions into $d+1$ nonempty blocks); $d\ge1$ is required for $\Omega^{d-1}$.
-- source:
--   Parzanchevski, Rosenthal and Tessler, Isoperimetric inequalities in simplicial complexes, arXiv:1207.0638v3, p. 12, §4.1, equation (4.2), with Definition 2.1 (p. 8)

import Mathlib
import Definitions.Def_SimplicialIso_Cheeger_Setting

namespace SimplicialIso.Cheeger

theorem eq_4_2 (n d : ℕ) (hd : 1 ≤ d) (hn : d + 1 ≤ n) (X : Complex n d) :
    ∃ μ : ℝ, IsCycleEigenvalue (upLap X) μ ∧
      (∀ ν : ℝ, IsCycleEigenvalue (upLap X) ν → μ ≤ ν) ∧
      ∀ f ∈ cycles n d,
        μ * inner ℝ f f ≤ inner ℝ (upLap X f) f ∧
        inner ℝ (upLap X f) f = inner ℝ (cobdTop X f) (cobdTop X f) := by sorry

end SimplicialIso.Cheeger
