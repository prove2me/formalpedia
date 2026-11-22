-- Prove2me | Theorems.Thm_PHarmLimit
-- name    : PHarmLimit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:12:19.550819+00:00
-- url     : https://prove2.me/theorems/424590c3-c0c2-46a4-8619-98965ff4483e
-- title:
--   PHarm Limit: PHarm Limit
-- statement:
--   Limit passage in the weak `p`-Laplace equation.  If every `u n` is `p`-harmonic
--   on `Ω` with weak gradient `g n`, and `u n → U`, `g n → G` uniformly on every compact
--   subset of `Ω`, then `U` is `p`-harmonic on `Ω` with weak gradient `G`.
--
--   The paper performs exactly this passage twice: once to see that the blow-up limit
--   `P_m` of a rigidity argument is `p`-harmonic, and once to see that every member of
--   the compact family in the high-order growth section is `p`-harmonic.  The step that
--   needs care is the flux term, since the convergence happens across critical points
--   where the scalar factor of `PFlux p` is unbounded; `PFluxContinuity` is what makes
--   it work.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/PHarmLimit.lean#L15-L279
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/PHarmLimit.lean#L15-L279

import Definitions.Def_PHigherOrder_IsPHarm
import Definitions.Def_PHigherOrder_PFluxContinuity
import Definitions.Def_PHigherOrder_VanishingOffTsupport
import Definitions.Def_PHigherOrder_PHarmLimit
import Theorems.Thm_PFluxContinuity
import Theorems.Thm_VanishingOffTsupport

set_option autoImplicit false

theorem PHarmLimit (p : ℝ) (hp : 1 < p) (hp2 : p < 2) (Ω : Set Plane)
    (u : ℕ → Plane → ℝ) (g : ℕ → Plane → Plane) (U : Plane → ℝ) (G : Plane → Plane)
    (hn : ∀ n : ℕ, IsPHarm p Ω (u n) (g n))
    (hU : ∀ K : Set Plane, K ⊆ Ω → IsCompact K → TendstoUniformlyOn u U Filter.atTop K)
    (hG : ∀ K : Set Plane, K ⊆ Ω → IsCompact K → TendstoUniformlyOn g G Filter.atTop K) :
    IsPHarm p Ω U G := by sorry
