-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Pj_meanK_mono__4cdf7a0dca76
-- name    : P2M_Formalism_L2_Pj_meanK_mono__4cdf7a0dca76
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:59:25.745874+00:00
-- url     : https://prove2.me/theorems/316b19a9-068d-4513-b117-0ffdeb34afc2
-- title:
--   P2 M Formalism L2 Pj mean K mono  4cdf7a0dca76: P2 M Formalism L2 Pj mean K mono  4cdf7a0dca76
-- statement:
--   The P2 M Formalism L2 Pj mean K mono  4cdf7a0dca76 construction uses the P2 M Formalism L2 Pj mean K mono  4cdf7a0dca76 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/AxHSup.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/AxHSup.lean#L43-L47

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompHt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PTNonempty
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AxHSup
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
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]
variable {h : GenFrEx Xo c} {fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ}
  {yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))}

theorem P2M_Formalism_L2_Pj_meanK_mono__4cdf7a0dca76 {K : Type} [Field K] [NumberField K] {F G : (K →+* ℂ) → ℝ} (hFG : ∀ sg, F sg ≤ G sg) :
    meanK F ≤ meanK G := by sorry

alias «Formalism».«L2».«Pj».«meanK_mono'» := P2M_Formalism_L2_Pj_meanK_mono__4cdf7a0dca76
