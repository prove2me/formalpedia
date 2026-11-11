-- Prove2me | Theorems.Thm_UPPIntersection_Halfspaces_lemma_4_4
-- name    : UPPIntersection.Halfspaces.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T16:27:40.504197+00:00
-- url     : https://prove2.me/theorems/4897ee9e-43b9-4c33-b760-e2ee2aeece29
-- title:
--   Lemma 4.4 — degree lower bound for sign representations of $Q_k$ on $I_\eta^k$
-- statement:
--   There is a universal constant $C>0$ such that:
--
--   1. for every $\eta\in(0,1)$ and integer $k\ge2$, if a real polynomial $q$ in $k$ variables of total degree $D$ sign-represents $Q_k$ on $I_\eta^k$ (that is, $q(s)\,Q_k(s)>0$ for all $s\in I_\eta^k$), then $D>2C\ln(1/\eta)$;
--   2. consequently, for every integer $k\ge2$ and every integer $D\ge1$, with $\eta=2e^{-D/C}$ no polynomial of total degree at most $D$ sign-represents $Q_k$ on $I_\eta^k$.
--
--   Both clauses are stated. The second is the form used in Lemma 4.1, where it is contradicted by a polynomial built from a large-coefficient approximate sign representation.
--
--   Differences from the source: none.
-- source:
--   Mark Bun, Mandar Juvekar, STOC 2027 submission #478 (October 2026), p. 22, Lemma 4.4 (and its proof on p. 22); PDF page = printed page; source.pdf SHA-256 1d258c38a48636b0aa03fa9dfce0ba5e367df8b9c55ee6e67f9f3b6f76e0d388

import Mathlib
import Definitions.Def_UPPIntersection_Halfspaces_Polynomials

namespace UPPIntersection.Halfspaces

theorem lemma_4_4 : ∃ C : ℝ, 0 < C ∧
    (∀ η : ℝ, 0 < η → η < 1 → ∀ k : ℕ, 2 ≤ k → ∀ q : MvPolynomial (Fin k) ℝ,
      (∀ s : Fin k → ℝ, (∀ i, s i ∈ bandI η) → 0 < MvPolynomial.eval s q * orthantQ s) →
      2 * C * Real.log (1 / η) < q.totalDegree) ∧
    (∀ k : ℕ, 2 ≤ k → ∀ D : ℕ, 1 ≤ D → ∀ q : MvPolynomial (Fin k) ℝ, q.totalDegree ≤ D →
      ¬ ∀ s : Fin k → ℝ, (∀ i, s i ∈ bandI (2 * Real.exp (-(D : ℝ) / C))) →
        0 < MvPolynomial.eval s q * orthantQ s) := by sorry

end UPPIntersection.Halfspaces
