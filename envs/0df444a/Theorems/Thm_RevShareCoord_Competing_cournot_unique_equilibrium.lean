-- Prove2me | Theorems.Thm_RevShareCoord_Competing_cournot_unique_equilibrium
-- name    : RevShareCoord.Competing.cournot_unique_equilibrium
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T00:53:09.29744+00:00
-- url     : https://prove2.me/theorems/836120ff-4dee-4b87-972e-692814a3f137
-- title:
--   Sec. 4.1.2 — Cournot retailers at a common price w: the unique equilibrium is q_i^N = (1 − w)/(2 + β(n − 1))
-- statement:
--   Let $n$ symmetric retailers have the Cournot revenues (7),
--   $$R_i(\bar q) = q_i\Big(1 - q_i - \beta \sum_{j\ne i} q_j\Big), \qquad 0 \le \beta < 1,$$
--   and let all of them pay the same wholesale price $w < 1$, with no revenue sharing. Then the retailers' quantity game has exactly one Nash equilibrium in order quantities, the symmetric profile
--   $$q_i^N = \frac{1-w}{2+\beta(n-1)}, \qquad i = 1,\dots,n.$$
--   That is, this profile is an equilibrium, and every equilibrium (symmetric or not) equals it.
--
--   The parameters $\beta$ and $n$ measure the intensity of competition, and this closed form is the basis of the paper's efficiency comparison in Section 4.1.2.
--
--   **Formalization Note** The page leaves $w < 1$ implicit; it is what makes the equilibrium quantity positive (for $w \ge 1$ every retailer stocks nothing). The page's standing $w > 0$ is not needed and is not assumed. Uniqueness is stated among all profiles in $[0,\infty)^n$, as the page claims.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 19 (PDF p. 20), Section 4.1.2, second paragraph

import Mathlib
import Definitions.Def_RevShareCoord_Competing_Game
import Definitions.Def_RevShareCoord_Competing_Cournot

namespace RevShareCoord.Competing

open Finset

/-- **Sec. 4.1.2, the Cournot equilibrium (p. 19).** Take `n` symmetric retailers with the
Cournot revenues (7), `Rᵢ(q̄) = qᵢ(1 − qᵢ − β Σ_{j≠i} qⱼ)`, `0 ≤ β < 1`, all paying the same
wholesale price `w < 1` with no revenue sharing. Then the symmetric profile with
`q_i^N = (1 − w)/(2 + β(n − 1))` is a Nash equilibrium, and it is the only Nash equilibrium. -/
theorem cournot_unique_equilibrium {n : ℕ} (β w : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hw : w < 1) :
    IsNashEquilibrium (cournotRevenue β) 1 (fun _ : Fin n => w) (fun _ => cournotQN β n w) ∧
      ∀ q : Fin n → ℝ, IsNashEquilibrium (cournotRevenue β) 1 (fun _ => w) q →
        q = fun _ => cournotQN β n w := by sorry

end RevShareCoord.Competing
