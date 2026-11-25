-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Pj_divFin_of_lawA3__ca8ab2190a30
-- name    : P2M_Formalism_L2_Pj_divFin_of_lawA3__ca8ab2190a30
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:06:50.951796+00:00
-- url     : https://prove2.me/theorems/6c699fbd-f779-428b-8e89-154c22e0b2c2
-- title:
--   P2 M Formalism L2 Pj div Fin of law A3  ca8ab2190a30: P2 M Formalism L2 Pj div Fin of law A3  ca8ab2190a30
-- statement:
--   The P2 M Formalism L2 Pj div Fin of law A3  ca8ab2190a30 construction uses the P2 M Formalism L2 Pj div Fin of law A3  ca8ab2190a30 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/DivFinOfLawA3.lean#L48-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/DivFinOfLawA3.lean#L48-L77

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

theorem P2M_Formalism_L2_Pj_divFin_of_lawA3__ca8ab2190a30 (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (hord : ∀ Z v, d.ord Z v = ordC (δ Z v) v) (h : LawA3' d) : DivFin d := by sorry

alias «Formalism».«L2».«Pj».«divFin_of_lawA3'» := P2M_Formalism_L2_Pj_divFin_of_lawA3__ca8ab2190a30
