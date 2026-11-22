-- Prove2me | Theorems.Thm_RudinSquares_square_positions_24_1_and_8_1
-- name    : RudinSquares.square_positions_24_1_and_8_1
-- status  : Proved
-- author  : @LG
-- created : 2026-11-18T18:22:07.135379+00:00
-- url     : https://prove2.me/theorems/4f8b7eab-f140-433f-a19b-d750426443b2
-- title:
--   Section 1.1(i)–(ii) — square positions of $24n+1$ and $8n+1$
-- statement:
--   The square positions of the two extremal progressions are classical figurate sequences (Section 1.1, items (i)–(ii)).
--
--   (i) The progression $24n+1$ is a square exactly at the generalized pentagonal numbers:
--   $$S(24,1)=\{GP_k\}_{k\in\mathbb Z},\qquad GP_k=\frac{k(3k-1)}{2}.$$
--
--   (ii) The progression $8n+1$ is a square exactly at the triangular numbers:
--   $$S(8,1)=\{T_k\}_{k\in\mathbb N},\qquad T_k=\frac{k(k+1)}{2}.$$
--
--   These identities explain why $24n+1$ and $8n+1$ recur as extremal progressions and give the closed form $Q(N;24,1)=\sqrt{8N/3}+O(1)$ used in the strong conjecture.
-- source:
--   E. González-Jiménez and X. Xarles, 'On a conjecture of Rudin on squares in arithmetic progressions', LMS J. Comput. Math. 17(1) (2014) 58–76, doi:10.1112/S1461157013000259, §1.1 (Notation), items (i)–(ii), p. 59.

import Mathlib
import Definitions.Def_RudinSquares_Defs

namespace RudinSquares
theorem square_positions_24_1_and_8_1 :
    S 24 1 = {n : ℕ | ∃ k : ℤ, (n : ℤ) = GP k} ∧
    S 8 1 = Set.range T := by sorry
end RudinSquares
