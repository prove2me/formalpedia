-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_der_monomial
-- name    : PositivityTheory.SiegelWeilFormula.KSplit.der_monomial
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:03:29.019894+00:00
-- url     : https://prove2.me/theorems/382a2df4-92cb-4c71-a9f8-8119661e7914
-- title:
--   KSplit: der monomial
-- statement:
--   The KSplit construction uses the der monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean#L128-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean#L128-L143

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ThetaSplitting_ActUDiagMonomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KSplit
open PositivityTheory.Rg.Sw
variable {m n : ℕ}

theorem PositivityTheory.SiegelWeilFormula.KSplit.der_monomial (D : Derivation ℂ (PX m n) (PX m n)) (w : Fin m × Fin n × Bool → ℂ)
    (hD : ∀ k, D (X k) = C (w k) * X k) (s : Fin m × Fin n × Bool →₀ ℕ) :
    D (monomial s 1) = C (s.sum fun k e => (e : ℂ) * w k) * monomial s 1 := by sorry
