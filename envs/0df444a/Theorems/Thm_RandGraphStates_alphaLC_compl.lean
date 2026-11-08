-- Prove2me | Theorems.Thm_RandGraphStates_alphaLC_compl
-- name    : RandGraphStates.alphaLC_compl
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:02:03.193231+00:00
-- url     : https://prove2.me/theorems/b99e7cf0-594a-4ab7-82f6-1f1bacefd7ef
-- title:
--   §4.1, display: $|\alpha_{\mathrm{LC}}(G)-\alpha_{\mathrm{LC}}(\overline G)|\le 1$
-- statement:
--   For every finite graph $G$ with complement $\overline G$,
--   $$
--   \bigl|\alpha_{\mathrm{LC}}(G)-\alpha_{\mathrm{LC}}(\overline G)\bigr|\le 1 .
--   $$
--   Since $\overline{G_{n,p}}$ has the law of $G_{n,1-p}$, this is the step that lets the paper work with $p=p_-\le 1/2$ up to a constant.
--
--   Differences from the source:
--   - encoding: |αLC(G) − αLC(Ḡ)| as a real number → the difference taken in ℤ; reason: the same value; avoids truncated subtraction in ℕ
-- source:
--   Chen, Ferber, Goodenough, Sales, Entanglement in random graph states, manuscript (November 2026), §4.1, display, p.18

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

/-- **§4.1, display, p.18.** Complementing a finite graph changes `αLC` by at most `1`:
`|αLC(G) - αLC(Ḡ)| ≤ 1`.

Source: Chen, Ferber, Goodenough, Sales, *Entanglement in random graph states*, manuscript (November 2026), §4.1, display, p.18.

**Formalization Note.** The difference is taken in `ℤ`. -/
theorem alphaLC_compl {V : Type*} [Fintype V] (G : SimpleGraph V) :
    |(alphaLC G : ℤ) - (alphaLC Gᶜ : ℤ)| ≤ 1 := by sorry

end RandGraphStates
