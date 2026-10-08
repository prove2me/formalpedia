-- Prove2me | Theorems.Thm_ScatCaps_Caps_theorem_1_3
-- name    : ScatCaps.Caps.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:05:59.693719+00:00
-- url     : https://prove2.me/theorems/13804389-6e69-4f8a-85d1-3a1b7e325f29
-- title:
--   Theorem 1.3, p. 4 — for q = 2^t, t even, n ≥ 4 even, AG(n, q) has a complete cap of size 2√(q^{n−1})
-- statement:
--   Let $q = 2^t$ with $t$ even, and let $n \ge 4$ be even. Then there exists a complete cap $S$ in the affine Galois space $AG(n, q)$ of size
--
--   $$|S| = 2\sqrt{q}^{\,n-1} .$$
--
--   Compared with the trivial lower bound $\sqrt 2 \cdot \sqrt q^{\,n-1}$ for the size of a complete cap, this shows that the bound is sharp up to a constant factor in even dimension $n \ge 4$ when $q$ is an even square.
--
--   **Formalization Note** $AG(n, q)$ is `Fin n → K` with $|K| = 2^t$; a complete cap is a set with no three distinct collinear points (collinearity over $K$) to which no further point of $AG(n, q)$ can be added. The size $2\sqrt q^{\,n-1}$ is written $2 \cdot 2^{t(n-1)/2}$ with natural-number division, which is exact because $t$ is even. The size is stated as an equality: the empty set is a cap and complete caps of some size always exist, so the exact size is the content.
-- source:
--   Bartoli, Giulietti, Marino & Polverino, Maximum scattered linear sets and complete caps in Galois spaces, arXiv:1512.07467v1, p. 4, Theorem 1.3

import Mathlib
import Definitions.Def_ScatCaps_Caps_Model

namespace ScatCaps.Caps

theorem theorem_1_3 (K : Type*) [Field K] [Fintype K] (t n : ℕ)
    (hK : Fintype.card K = 2 ^ t) (ht : Even t) (hn : 4 ≤ n) (hne : Even n) :
    ∃ S : Set (Fin n → K), IsCompleteCap S ∧ S.ncard = 2 * 2 ^ (t * (n - 1) / 2) := by sorry

end ScatCaps.Caps
