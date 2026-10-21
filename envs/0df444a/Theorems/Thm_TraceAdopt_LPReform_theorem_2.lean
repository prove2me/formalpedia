-- Prove2me | Theorems.Thm_TraceAdopt_LPReform_theorem_2
-- name    : TraceAdopt.LPReform.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:37:04.68478+00:00
-- url     : https://prove2.me/theorems/7f181a45-3c76-4f90-be06-a196d1ec5679
-- title:
--   Theorem 2, p. 18 — an exact LP reformulation of MIN-SCTM of fixed-parameter size
-- statement:
--   There is one absolute constant $C>0$ such that every instance of MIN-SCTM on a hypergraph of treewidth at most $\omega$ has a linear system $Az\ge b$, fixed independently of the seeding costs $w$, with at most
--
--   $$2^{C(\omega+1)^2}(\vartheta_{\max}+1)^{C(\omega+1)}C(n+m+1)$$
--
--   variables and constraints in total. Writing $z=(x,y)$ with $x$ indexed by firms, the projection of its feasible region onto $x$ is the convex hull of the indicators of fully activating seed sets. Consequently, for every real cost vector $w$, minimizing $\sum_iw_ix_i$ over that same LP attains $\mathrm{OPT}(w)$.
--
--   This is an exact, cost-independent LP reformulation whose size is fixed-parameter tractable in the hypergraph treewidth and $\vartheta_{\max}$.
--
--   **Formalization Note** The bound encodes the $2^{O(\omega^2)}\vartheta_{\max}^{O(\omega)}O(n+m)$ statement following Theorem 2 on p. 18, rather than its preceding displayed bracket, whose exponents do not match the proof's composition of bounds. The shifts by one handle small parameters. Treewidth equality is read as an upper bound. The §3.1 standing assumptions include connectedness as the paper's without-loss-of-generality convention.
-- source:
--   Blaettchen, Calmon & Hall, Traceability Technology Adoption in Supply Chain Networks, arXiv:2104.14818v4, p. 18, Theorem 2 and following sentence; p. 41, proof

import Definitions.Def_TraceAdopt_LPReform_Model
import Definitions.Def_TraceAdopt_LPReform_LinearSystem

namespace TraceAdopt.LPReform

/-- Theorem 2, p. 18, in the asymptotic form stated in the sentence following
the display: an objective-independent LP extended formulation for MIN-SCTM. -/
theorem theorem_2 :
    ∃ C : ℕ, 0 < C ∧
      ∀ (I : Instance), I.Standing → ∀ ω : ℕ, HypTreewidthLE I ω →
        ∃ (N K : ℕ) (A : Matrix (Fin K) (Fin I.n ⊕ Fin N) ℝ)
          (b : Fin K → ℝ),
          I.n + N + K ≤
            2 ^ (C * (ω + 1) ^ 2) *
              (varthetaMax I + 1) ^ (C * (ω + 1)) *
              (C * (I.n + I.m + 1)) ∧
          {x : Fin I.n → ℝ | ∃ y : Fin N → ℝ, LinFeasible A b x y} =
            convexHull ℝ (ind '' {S : Finset (Fin I.n) | FullyActivates I S}) ∧
          ∀ w : Fin I.n → ℝ,
            IsLeast {v : ℝ | ∃ x y, LinFeasible A b x y ∧
              v = ∑ i, w i * x i} (OPT I w) := by sorry

end TraceAdopt.LPReform
