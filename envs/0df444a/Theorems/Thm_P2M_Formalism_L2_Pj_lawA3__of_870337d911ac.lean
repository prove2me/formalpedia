-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Pj_lawA3__of_870337d911ac
-- name    : P2M_Formalism_L2_Pj_lawA3__of_870337d911ac
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:57:50.040526+00:00
-- url     : https://prove2.me/theorems/9e466d14-494b-41a9-b0aa-c7a7368bc412
-- title:
--   P2 M Formalism L2 Pj law A3  of 870337d911ac: P2 M Formalism L2 Pj law A3  of 870337d911ac
-- statement:
--   The P2 M Formalism L2 Pj law A3  of 870337d911ac construction uses the P2 M Formalism L2 Pj law A3  of 870337d911ac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/DivFinOfLawA3.lean#L21-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/DivFinOfLawA3.lean#L21-L46

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompHt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_DivFinOfLawA3
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]
variable (d : Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z))

theorem P2M_Formalism_L2_Pj_lawA3__of_870337d911ac (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (hord : ∀ Z v, d.ord Z v = ordC (δ Z v) v) (hD : DivFin d) (hF : FrShFin d δ) : LawA3' d := by sorry

alias «Formalism».«L2».«Pj».«lawA3'_of» := P2M_Formalism_L2_Pj_lawA3__of_870337d911ac
