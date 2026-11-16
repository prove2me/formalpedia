-- Prove2me | Theorems.Thm_UPPIntersection_Halfspaces_Supplement_lemma_8_3
-- name    : UPPIntersection.Halfspaces.Supplement.lemma_8_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:04:19.459353+00:00
-- url     : https://prove2.me/theorems/48944554-f534-4fa6-b90a-01afd8d29c9c
-- title:
--   Lemma 8.3 — a degree-$O(k^2\log(1/\eta))$ polynomial sign-representing $Q_k$ on $I_\eta^k$
-- statement:
--   There is a universal constant $K>0$ such that for every $\eta\in(0,1/2)$ and every $k\ge1$ there is a real polynomial $q$ in $k$ variables of total degree at most $Kk^2\log(1/\eta)$, i.e. of degree $O(k^2\log(1/\eta))$, with
--   $$Q_k(s)\cdot q(s)>0\qquad\text{for every }s\in I_\eta^k,$$
--   where $I_\eta=[-1,-\eta]\cup[\eta,1]$ and $\log$ is base 2.
--
--   This sign-representation of the orthant indicator, built from rational approximations of the sign function, is the source of all the upper bounds of §8: it turns into the sign-rank bound of Lemma 8.4.
--
--   Differences from the source:
--   - encoding: degree O(k² log(1/η)) → total degree at most K k² log₂(1/η) for one universal K > 0 chosen before η and k; reason: the O-constant is universal in the source; log₂(1/η) > 1 on (0,1/2), so no additive constant is needed
-- source:
--   Mark Bun, Mandar Juvekar, STOC 2027 submission #478 (October 2026), p. 31, Lemma 8.3 (proof on pp. 31–32); PDF page = printed page; source.pdf SHA-256 1d258c38a48636b0aa03fa9dfce0ba5e367df8b9c55ee6e67f9f3b6f76e0d388

import Mathlib
import Definitions.Def_UPPIntersection_Halfspaces_Polynomials

namespace UPPIntersection.Halfspaces.Supplement

/-- Bun–Juvekar, Lemma 8.3 (p. 31). There is a universal constant `K > 0` such that for every
`η ∈ (0, 1/2)` and `k ≥ 1` some real polynomial `q` in `k` variables of total degree at most
`K k² log₂(1/η)` (i.e. `O(k² log(1/η))`) satisfies `Q_k(s) · q(s) > 0` for every `s ∈ I_η^k`. -/
theorem lemma_8_3 : ∃ K : ℝ, 0 < K ∧ ∀ η : ℝ, 0 < η → η < 1 / 2 → ∀ k : ℕ, 1 ≤ k →
    ∃ q : MvPolynomial (Fin k) ℝ, (q.totalDegree : ℝ) ≤ K * (k : ℝ) ^ 2 * Real.logb 2 (1 / η) ∧
      ∀ s : Fin k → ℝ, (∀ i, s i ∈ bandI η) → 0 < orthantQ s * MvPolynomial.eval s q := by sorry

end UPPIntersection.Halfspaces.Supplement
