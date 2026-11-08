-- Prove2me | Theorems.Thm_RandGraphStates_lemma_4_14
-- name    : RandGraphStates.lemma_4_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:02:31.229411+00:00
-- url     : https://prove2.me/theorems/24b2ab3f-e586-4999-9064-c83ebbfb452c
-- title:
--   Lemma 4.14: coarse nullity tail
-- statement:
--   For $0<p<1$ and every $0\le t\le m$,
--   $$
--   \pi^p_m(t)\le\binom mt\,p_+^{\binom t2}.
--   $$
--   This bound holds for all $m$ and handles the small principal submatrices in the union bound of Theorem 4.17.
--
--   Differences from the source: none.
-- source:
--   Chen, Ferber, Goodenough, Sales, Entanglement in random graph states, manuscript (November 2026), Lemma 4.14, p.28

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

/-- **Lemma 4.14** (coarse nullity tail). For every `0 ≤ t ≤ m`, `π^p_m(t) ≤ C(m,t) p₊^{C(t,2)}`.

Source: Chen, Ferber, Goodenough, Sales, *Entanglement in random graph states*, manuscript (November 2026), Lemma 4.14, p.28.

**Formalization Note.** `0 < p < 1` is the standing assumption of §4, p.17. -/
theorem lemma_4_14 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (m t : ℕ) (htm : t ≤ m) :
    piTail p m t ≤ (m.choose t : ℝ) * pPlus p ^ (t.choose 2) := by sorry

end RandGraphStates
