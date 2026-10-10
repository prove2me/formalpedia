-- Prove2me | Theorems.Thm_TitiusBode_representations_agree
-- name    : TitiusBode.representations_agree
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:26:52.871344+00:00
-- url     : https://prove2.me/theorems/1e906f2a-6ee6-4bfb-bb04-ac58b1afdad9
-- title:
--   Original formulation — the four representations of the Titius–Bode rule agree
-- statement:
--   Let $x = 0, 3, 6, 12, \dots$ be the sequence $x_0 = 0$, $x_1 = 3$, $x_{i+2} = 2x_{i+1}$. Then:
--
--   1. the original values $4 + x_i$ (Earth $= 10$) equal $4 + 3\cdot 2^{n}$ with $n = -\infty$ for $i = 0$ and $n = i - 1$ for $i \ge 1$:
--   $$4 + x_0 = 4 + 3\cdot 2^{-\infty}, \qquad 4 + x_{n+1} = 4 + 3\cdot 2^{n}\quad (n \in \mathbb N);$$
--   2. dividing by $10$ converts to astronomical units: $0.4 + 0.3\cdot 2^n = (4 + 3\cdot 2^n)/10$ for all $n \in \{-\infty, 0, 1, \dots\}$;
--   3. for $n \in \mathbb N$ the au form coincides with the canonical form $a_n = 0.4 + 0.3\cdot 2^n$.
--
--   This records that the representations given in the section "Original formulation" of the source describe the same predicted distances.
-- source:
--   Wikipedia, "Titius–Bode law", revision oldid=1372822920, https://en.wikipedia.org/w/index.php?title=Titius%E2%80%93Bode_law&oldid=1372822920, section "Original formulation"

import Definitions.Def_TitiusBode_Defs
import Mathlib
open Filter Topology

namespace TitiusBode
theorem representations_agree :
    ((tbOriginal 0 : ℝ) = tbTenths ⊥ ∧
      ∀ n : ℕ, (tbOriginal (n + 1) : ℝ) = tbTenths (n : WithBot ℕ)) ∧
    (∀ n : WithBot ℕ, tbAU n = tbTenths n / 10) ∧
    (∀ n : ℕ, tbAU (n : WithBot ℕ) = tbCanonical n) := by sorry
end TitiusBode
