-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_etaLt_mul_right
-- name    : PositivityTheory.Rg.Sw.LC.B3.etaLt_mul_right
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:56:50.683794+00:00
-- url     : https://prove2.me/theorems/a4883fe0-f198-5efe-91e2-c6e3d08d922b
-- title:
--   B3: eta Lt mul right
-- statement:
--   The B3 construction uses the eta Lt mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SymmetricFiltrationIffSupported.lean#L128-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SymmetricFiltrationIffSupported.lean#L128-L135

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivPowMonomial
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymmetricFiltrationIffSupported
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.B3
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.CoreBb
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.LC.B3.etaLt_mul_right {u v : Sym m n} {d₁ d₂ : ℕ} (hu : EtaLt u d₁) (hv : EtaLe v d₂) : EtaLt (u * v) (d₁ + d₂) := by sorry
