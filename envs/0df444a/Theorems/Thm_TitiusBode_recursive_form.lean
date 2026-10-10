-- Prove2me | Theorems.Thm_TitiusBode_recursive_form
-- name    : TitiusBode.recursive_form
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:27:21.200985+00:00
-- url     : https://prove2.me/theorems/7fe76217-8f70-43ae-b1b8-f93296ce3e8a
-- title:
--   Recursive form — $a_{n+1} = 2a_n - 0.4$, and the index shift of $a_0 = 0.55$
-- statement:
--   Let $a_n = 0.4 + 0.3\cdot 2^n$ ($n \in \mathbb N$) be the canonical Titius–Bode form, and let $b$ be the recursive sequence printed in the source, $b_0 = 0.55$ and $b_{n+1} = 2b_n - 0.4$. Then
--
--   1. the canonical form satisfies the recursion: $a_{n+1} = 2a_n - 0.4$ for all $n$;
--   2. the printed recursion reproduces the canonical form shifted by one index: $b_{n+1} = a_n$ for all $n$;
--   3. $b_0 \ne a_0$ (indeed $b_0 = 0.55$ while $a_0 = 0.7$).
--
--   The source states that the canonical form "also has a recursive form $a_{n+1} = 2a_n - 0.4$, where $a_0 = 0.55$". Read literally with the same index, that claim is false; this milestone records the correct relationship.
-- source:
--   Wikipedia, "Titius–Bode law", revision oldid=1372822920, https://en.wikipedia.org/w/index.php?title=Titius%E2%80%93Bode_law&oldid=1372822920, section "Original formulation", last paragraph

import Definitions.Def_TitiusBode_Defs
import Mathlib
open Filter Topology

namespace TitiusBode
theorem recursive_form :
    (∀ n : ℕ, tbCanonical (n + 1) = 2 * tbCanonical n - 0.4) ∧
    (∀ n : ℕ, tbRecursive (n + 1) = tbCanonical n) ∧
    tbRecursive 0 ≠ tbCanonical 0 := by sorry
end TitiusBode
