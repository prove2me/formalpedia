-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_Supplement_equality_free_pp_sensitivity_transfer
-- name    : StabilityDichotomies.Solvability.Supplement.equality_free_pp_sensitivity_transfer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:36:51.326377+00:00
-- url     : https://prove2.me/theorems/6ea4244c-3f77-4c68-b6e9-9d734e3b0236
-- title:
--   Lemma 4.10 — Equality-free pp transfer with exact size and sensitivity factor
-- statement:
--   Let Λ and Γ be finite Boolean constraint languages. Fix integers a ≥ 1, b ≥ 0 and D ≥ 1. Every relation of Λ is assumed to have an equality-free primitive-positive definition over Γ with at most a atomic occurrences and at most b existential variables. Fix ε₀ ∈ (0,1), c₀ > 0 and an unbounded set N ⊆ ℕ≥1 such that every randomized (1−ε₀)-approximation algorithm B for CSP(Λ), and every n ∈ N, admit a satisfiable Λ-instance with n variables, at most Dn constraints and average sensitivity at least c₀n.
--
--   Put η=ε₀/(2a). Every randomized algorithm A that (1−η)-approximates CSP(Γ), and every n ∈ N, admit a satisfiable instance I′=(V′,C′) over Γ satisfying simultaneously
--
--   $$|V'|=(1+bD)n,\qquad |C'|\le aDn,\qquad
--   \operatorname{ASens}(A,I')\ge \frac{c_0\eta^{a-1}}{a}\,n.$$
--
--   The coefficient and n in the last expression refer to the original size, rather than the enlarged variable count. All source witnesses and pp bounds are fixed before either solver. The theorem includes a=1 and b=0, empty conjunctions where they correctly define a relation, and repeated variables and atomic occurrences. No computational, symmetry, bounded-degree or finite-probability restriction is imposed on either solver.
--
--   This is the quantitative transfer lemma used with Proposition 4.11 to obtain Theorem 4.1's approximation lower branch. The exact expansion factor, sparsity bound and positive sensitivity coefficient are all retained. **Formalization Note** The target carrier has the exact enlarged size as its type, so unused existential variables remain part of the instance.
--
--   Differences from the source:
--   - encoding: a finite variable set V of cardinality n → the carrier Fin n; reason: finite carriers are represented by numbered variables with unrestricted scopes, including repeated and isolated variables
--   - encoding: integers a ≥ 1, b ≥ 0 and D ≥ 1, with an unbounded N contained in ℕ≥1 → natural counts a, b, D with explicit 1 ≤ a and 1 ≤ D, and N.Infinite together with ∀ n ∈ N, 1 ≤ n; reason: these types and bounds represent exactly the source integer domains and positive size set
-- source:
--   Chunyang Wang, Yuichi Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535 (October 2026), canonical source.pdf, SHA-256 9eeb0875db685945a8b4c78bc4d30bfdbf3289a943d06f464836530d0eb22467. p.22, Lemma 4.10 (entire statement); proof pp.22–23, especially (11) and its concluding exact-size assertion.

import Definitions.Def_StabilityDichotomies_Approximability_Core
import Definitions.Def_StabilityDichotomies_Solvability_Supplement_EqualityFreePP

open scoped Classical

namespace StabilityDichotomies.Solvability.Supplement

/-- Lemma 4.10, p.22. The source lower-bound witnesses are fixed before all source solvers.
The target carrier has exactly (1+bD)n elements, including every unused witness variable. -/
theorem equality_free_pp_sensitivity_transfer
    (Λ Γ : Language) (a b D : ℕ) (ha : 1 ≤ a) (hD : 1 ≤ D)
    (hdefinitions : HasBoundedEqualityFreePPDefinitions Λ Γ a b)
    (ε₀ c₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀_one : ε₀ < 1) (hc₀ : 0 < c₀)
    (N : Set ℕ) (hN : N.Infinite) (hN_pos : ∀ n ∈ N, 1 ≤ n)
    (hlower : ∀ B : Solver Λ, Approximates B ε₀ →
      ∀ n ∈ N, ∃ I : Instance Λ (Fin n),
        Satisfiable I ∧ I.constraints.card ≤ D * n ∧
          c₀ * (n : ℝ) ≤ averageSensitivity B I) :
    let η : ℝ := ε₀ / (2 * (a : ℝ))
    ∀ A : Solver Γ, Approximates A η →
      ∀ n ∈ N, ∃ I' : Instance Γ (Fin ((1 + b * D) * n)),
        Satisfiable I' ∧ I'.constraints.card ≤ a * D * n ∧
          (c₀ * η ^ (a - 1) / (a : ℝ)) * (n : ℝ) ≤
            averageSensitivity A I' := by sorry

end StabilityDichotomies.Solvability.Supplement
