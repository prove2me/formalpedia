-- Prove2me | Theorems.Thm_QuantumSepPoly_Frobenius_Supplement_lemma_6_7
-- name    : QuantumSepPoly.Frobenius.Supplement.lemma_6_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:54:20.989089+00:00
-- url     : https://prove2.me/theorems/ef2ad5be-935c-4107-a241-5fb071160fc4
-- title:
--   Lemma 6.7 — The ideal separable state passes the explicitly constructed acceptance operator with Tr(Mψ) ≥ 1 − ε/4
-- statement:
--   Let $I$ be a positive-size sparse Boolean two-CSP over a positive finite alphabet, and let $D$ be a probability law supported on assignments with value one. Fix source-admissible $\eta\in(0,1)$, $t\ge1$, rational $\varepsilon>0$, and the computed $k$, in the branch $4k\le n+m+2$. For the ideal $2k$-register state and the constructed acceptance operator,
--   $$\operatorname{Tr}(M\psi)\ge1-\varepsilon/4.$$
--   This is the ideal-state acceptance guarantee; it contains no hypothesis asserting that guarantee.
--
--   Differences from the source:
--   - generalization: satisfiable formula and the distribution supplied by Lemma 6.4 → any sparse Boolean CSP and any fully satisfying assignment law satisfying the stated sampler context where needed; reason: the constructed CSP and its single law D satisfy these hypotheses, so every source instance is included
--   - encoding: finite complex registers with one-based indices → zero-based finite function registers and explicit mixed-radix basis maps; reason: bijections preserve the source matrices and the specified bipartite cut
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), Lemma 6.7, p. 30 (PDF p. 30); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_Supplement_IdealState

open scoped BigOperators ENNReal

namespace QuantumSepPoly.Frobenius.Supplement

theorem lemma_6_7 (N A δ n m : ℕ) (η : ℝ) (t : ℕ) (ε : ℚ)
    (I : MaxCSP N 2 (Fin A)) (D : PMF (Fin N → Fin A)) (ξ : ℝ)
    (hN : 1 ≤ N) (hA : 1 ≤ A) (hI : Sparse I δ)
    (hη : 0 < η ∧ η < 1) (hp : Admissible η A δ ξ t ε)
    (hbranch : 4*registerCount N A ε ≤ n+m+2)
    (hD : ∀ z, D z ≠ 0 → cspValue I z = 1) :
    1-(ε : ℝ)/4 ≤ ((acceptance I (registerCount N A ε) *
      idealState (registerCount N A ε) D).trace).re := by sorry

end QuantumSepPoly.Frobenius.Supplement
