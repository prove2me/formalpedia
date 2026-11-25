-- Prove2me | Theorems.Thm_PI_WickFormula_Asm_dL_monomial_support
-- name    : PI.WickFormula.Asm.dL_monomial_support
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:43:47.792863+00:00
-- url     : https://prove2.me/theorems/17b03450-a161-5f27-87f4-12ac8b069569
-- title:
--   Asm: d L monomial support
-- statement:
--   The Asm construction uses the d L monomial support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/XdegLeTotalDegree.lean#L22-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/XdegLeTotalDegree.lean#L22-L34

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_DeltaEqGdelta
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_XdegLeTotalDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.WickFormula PI.WickFormula.Asm

theorem PI.WickFormula.Asm.dL_monomial_support {k : Type} [CommRing k] {r s : ℕ} (κ : Fin r → Fin s → k) (i : Fin r)
    (m : Fin r ⊕ Fin s →₀ ℕ) (c : k) (u : Fin r ⊕ Fin s →₀ ℕ)
    (hu : u ∈ (Gen.dL κ i (monomial m c)).support) : xdeg u ≤ xdeg m := by sorry
