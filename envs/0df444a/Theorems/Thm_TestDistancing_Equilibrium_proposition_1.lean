-- Prove2me | Theorems.Thm_TestDistancing_Equilibrium_proposition_1
-- name    : TestDistancing.Equilibrium.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:05.851632+00:00
-- url     : https://prove2.me/theorems/50a79e54-dc15-4183-88b7-c9be910c6859
-- title:
--   Proposition 1 — testing lowers infection on a fixed network
-- statement:
--   Fix any contact graph $G$ and agent $i$. For two testing policies $(\alpha_L,\alpha_H)\le(\alpha'_L,\alpha'_H)$ in $[0,1]^2$, compared coordinatewise,
--
--   $$P_i^{\mathrm{inf}}(G,\alpha'_L,\alpha'_H)\le P_i^{\mathrm{inf}}(G,\alpha_L,\alpha_H).$$
--
--   The network is held fixed; this result isolates the direct effect of additional testing on the cascade.
-- source:
--   Acemoglu, Makhdoumi, Malekian & Ozdaglar, Testing, Voluntary Social Distancing and the Spread of an Infection, NBER Working Paper 27483 (July 2020), https://www.nber.org/papers/w27483, p. 9 (PDF 11), Proposition 1

import Mathlib
import Definitions.Def_TestDistancing_Equilibrium_Model

namespace TestDistancing.Equilibrium

theorem proposition_1 (P : Params) (hP : P.Standing) {n : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) (α α' : ℝ × ℝ)
    (hα : α ∈ PolicySquare) (hα' : α' ∈ PolicySquare)
    (hle : PolicyLe α α') (i : Fin n) :
    PinfG P G α' i ≤ PinfG P G α i := by sorry

end TestDistancing.Equilibrium
