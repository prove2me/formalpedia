-- Prove2me | Theorems.Thm_P2M_Formalism_L2_PjFree_regular__int_f20b464cd2c4
-- name    : P2M_Formalism_L2_PjFree_regular__int_f20b464cd2c4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:42.501805+00:00
-- url     : https://prove2.me/theorems/54875573-44dc-4506-9021-872b1bcb906b
-- title:
--   P2 M Formalism L2 Pj Free regular  int f20b464cd2c4: P2 M Formalism L2 Pj Free regular  int f20b464cd2c4
-- statement:
--   The P2 M Formalism L2 Pj Free regular  int f20b464cd2c4 construction uses the P2 M Formalism L2 Pj Free regular  int f20b464cd2c4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RegPFree.lean#L45-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RegPFree.lean#L45-L49

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PtFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegLaw
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegPFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.PjFree
open Formalism.L2.Pj
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)
variable {Xo c}

theorem P2M_Formalism_L2_PjFree_regular__int_f20b464cd2c4 {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} (h : regular₂ Xo c U) {a n} (hd : Dom a n)
    {f : Rul Xo c} (hf : f ∈ cusp Xo c U a n)
    (h0 : ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f) :
    ∀ la, ∀ v ∈ valSet Xo c (trivialClassCondition Xo c) la, 0 ≤ v f := by sorry

alias «Formalism».«L2».«PjFree».«regular₂».«int» := P2M_Formalism_L2_PjFree_regular__int_f20b464cd2c4
