-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_sparse_large_diameter_obstruction
-- name    : StabilityDichotomies.Solvability.sparse_large_diameter_obstruction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:05:29.068327+00:00
-- url     : https://prove2.me/theorems/1c1d667e-9d19-4553-ab91-100a69e55a88
-- title:
--   Lemma 3.8 — sparse minimally unsatisfiable instance with large diameter
-- statement:
--   Let $\Gamma$ lack finite duality, and fix $\kappa_\Gamma=\sum_{R\in\Gamma}2^{r(R)}|R|^2>0$. For every integer $N\ge1$, there is a minimally unsatisfiable instance $F_N$ with connected incidence graph such that
--
--   $$|V(F_N)|\le4N,\qquad |C(F_N)|\le\kappa_\Gamma N,\qquad
--   \operatorname{diam}(G_{\rm inc}(F_N))\ge2N.$$
--
--   All properties hold simultaneously for the same instance. The fixed constant depends only on the language and is the witness defined in the source proof on p.14, with the exact occurrence count completed on p.15. It makes the printed $O_\Gamma(N)$ sparsity quantitative and supplies the denominator of the goal's linear sensitivity bound.
--
--   **Formalization Note** The finite carrier is relabelled as $\operatorname{Fin}(n)$. Extended graph diameter agrees with ordinary diameter on this finite connected graph.
--
--   Differences from the source:
--   - generalization: existence of a language-dependent constant κΓ → the fixed witness κΓ = sum over R in Γ of 2^arity(R) |R|²; reason: the proof defines this witness on p.14 and proves the corresponding count on p.15, so it instantiates the printed existential with all conclusions
--   - encoding: a finite instance with ordinary connected incidence diameter → a carrier Fin n and extended natural diameter on a connected finite incidence graph; reason: a bijective relabelling preserves constraints and minimality; extended diameter equals ordinary diameter here
-- source:
--   Chunyang Wang, Yuichi Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535 (October 2026), pp.14–15, Lemma 3.8 and its proof; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Solvability_FiniteDuality
import Definitions.Def_StabilityDichotomies_Solvability_Incidence

namespace StabilityDichotomies.Solvability

/-- Lemma 3.8, pp.14–15, with the proof's fixed kappa witness.
Finite carriers are relabelled as Fin n; no solver invariance is assumed. -/
theorem sparse_large_diameter_obstruction (Γ : Language) (hΓ : ¬ FiniteDuality Γ)
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ (n : ℕ) (F : Instance Γ (Fin n)),
      MinimallyUnsatisfiable F ∧ (incidenceGraph F).Connected ∧
      n ≤ 4 * N ∧ F.constraints.card ≤ kappa Γ * N ∧
      ((2 * N : ℕ) : ℕ∞) ≤ (incidenceGraph F).ediam := by sorry

end StabilityDichotomies.Solvability
