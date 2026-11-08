-- Prove2me | Theorems.Thm_RandGraphStates_lemma_4_6
-- name    : RandGraphStates.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:02:11.808596+00:00
-- url     : https://prove2.me/theorems/06133263-458d-4330-bc2e-078b6ddb4568
-- title:
--   Lemma 4.6: lower comparison with the uniform model
-- statement:
--   If $0<p\le1/2$, then for every $m$ and $t$,
--   $$
--   \Pr\bigl(\mathrm{Nullity}(A_m(p))\ge t\bigr)\ge\Pr\bigl(\mathrm{Nullity}(A_m(1/2))\ge t\bigr).
--   $$
--   This gives the first-moment lower bound in the second-moment argument of Theorem 4.20.
--
--   Differences from the source:
--   - encoding: every t → t a natural number; reason: negative t gives probability 1 on both sides
-- source:
--   Chen, Ferber, Goodenough, Sales, Entanglement in random graph states, manuscript (November 2026), Lemma 4.6, p.21

import Mathlib
import Definitions.Def_BollobasChromatic_Main_Setting
import Definitions.Def_RandGraphStates_alphaLC
import Definitions.Def_SquashedKey_KeyBoundFunction
import Definitions.Def_RandGraphStates_cEtaEps
import Definitions.Def_RandGraphStates_pMinus
import Definitions.Def_RandGraphStates_Cunif
import Definitions.Def_RandGraphStates_nullity
import Definitions.Def_RandGraphStates_piTail

set_option autoImplicit false

open BollobasChromatic.Main
open Filter Topology

namespace RandGraphStates

/-- **Lemma 4.6** (lower comparison with the uniform model). If `0 < p ≤ 1/2`, then for every `m`
and `t`, `Pr(Nullity(A_m(p)) ≥ t) ≥ Pr(Nullity(A_m(1/2)) ≥ t)`.

Source: Chen, Ferber, Goodenough, Sales, *Entanglement in random graph states*, manuscript (November 2026), Lemma 4.6, p.21. -/
theorem lemma_4_6 (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1 / 2) (m t : ℕ) :
    gnpProb m (1 / 2) (fun G => t ≤ nullity (adjF2 G)) ≤
      gnpProb m p (fun G => t ≤ nullity (adjF2 G)) := by sorry

end RandGraphStates
