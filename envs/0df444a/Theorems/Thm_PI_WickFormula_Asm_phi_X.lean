-- Prove2me | Theorems.Thm_PI_WickFormula_Asm_phi_X
-- name    : PI.WickFormula.Asm.phi_X
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:43:54.428906+00:00
-- url     : https://prove2.me/theorems/428f8731-7ebc-535b-b3d0-7d2d77a481b6
-- title:
--   Asm: phi X
-- statement:
--   The Asm construction uses the phi X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/XdegLeTotalDegree.lean#L88-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/XdegLeTotalDegree.lean#L88-L99

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
variable {k AA M : Type} [CommRing k] [Algebra ℚ k] [Ring AA] [Algebra k AA] [AddCommGroup M]
  [Module AA M] {r s : ℕ}
variable {a b : Fin r → AA} {a' b' : Fin s → AA} {κ : Fin r → Fin s → k} {σ₀ : M}

theorem PI.WickFormula.Asm.phi_X (h1 : OrdLin) (h2 : OrdX) (h4 : BComm) (H : Hyp a b a' b' κ σ₀) (i : Fin r)
    (R : MvPolynomial (Fin r ⊕ Fin s) k) :
    phiH h1 a b a' b' σ₀ (X (Sum.inl i) * R) =
      a i • phiH h1 a b a' b' σ₀ R + phiH h1 a b a' b' σ₀ (Gen.dL κ i R) := by sorry
