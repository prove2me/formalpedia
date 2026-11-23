-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_jet_ext__4fc5f26daf9f
-- name    : P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_jet_ext__4fc5f26daf9f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:43:55.796264+00:00
-- url     : https://prove2.me/theorems/5fa1bbbb-0343-4174-a354-813b644b6878
-- title:
--   P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Uniq Jet jet ext  4fc5f26daf9f: P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Uniq Jet jet ext  4fc5f26daf9f
-- statement:
--   The P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Uniq Jet jet ext  4fc5f26daf9f construction uses the P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Uniq Jet jet ext  4fc5f26daf9f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqJet.lean#L58-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqJet.lean#L58-L63

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_SpanXLeKerAevalZero
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqJet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
open MvPolynomial Formalism.L2.Pj
variable {R : Type} [CommRing R]

theorem P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_jet_ext__4fc5f26daf9f {κ : Type} {m : ℕ} {A : Type} [CommRing A] [Algebra R A] {f g : Jet R κ m →ₐ[R] A}
    (h : ∀ j, f (zz m j) = g (zz m j)) : f = g := by sorry

alias «Formalism».«MainNotions».«ModuliIntegralCharts».«H1».«ExpUniqJet».«jet_ext'» := P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_jet_ext__4fc5f26daf9f
