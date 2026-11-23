-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LC_Basic_degree_add__88e784869794
-- name    : P2M_PositivityTheory_Rg_Sw_LC_Basic_degree_add__88e784869794
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:16:23.076564+00:00
-- url     : https://prove2.me/theorems/24fc7597-75a8-430b-bcfc-5cfd95ba7d8c
-- title:
--   P2 M Positivity Theory Rg Sw LC Basic degree add  88e784869794: P2 M Positivity Theory Rg Sw LC Basic degree add  88e784869794
-- statement:
--   The P2 M Positivity Theory Rg Sw LC Basic degree add  88e784869794 construction uses the P2 M Positivity Theory Rg Sw LC Basic degree add  88e784869794 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/MapDomainFlpFlp.lean#L118-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/MapDomainFlpFlp.lean#L118-L119

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MapDomainFlpFlp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.Basic
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}

theorem P2M_PositivityTheory_Rg_Sw_LC_Basic_degree_add__88e784869794 (a b : Ix m n →₀ ℕ) : (a + b).degree = a.degree + b.degree := by sorry

alias «PositivityTheory».«Rg».«Sw».«LC».«Basic».«degree_add'» := P2M_PositivityTheory_Rg_Sw_LC_Basic_degree_add__88e784869794
