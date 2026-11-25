-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Cone_Vf_exists_decomp
-- name    : PositivityTheory.ThKG.Loc.Cone.Vf.exists_decomp
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:05:56.00581+00:00
-- url     : https://prove2.me/theorems/5104fc1d-c004-50f3-9af1-635b5e664104
-- title:
--   Vf: exists decomp
-- statement:
--   The Vf construction uses the exists decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ConeShifts/ExistsPowIdem.lean#L148-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ConeShifts/ExistsPowIdem.lean#L148-L230

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_ExistsPowIdem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Cone PositivityTheory.ThKG.Loc.Cone.Vf
open Matrix GlobalTheory.WeilM
variable {R A β : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) [Fintype β] [DecidableEq β]
variable {c} {J : Matrix β β A}

theorem PositivityTheory.ThKG.Loc.Cone.Vf.exists_decomp {Ji b b' f' : Matrix β β A} (hJ : J * Ji = 1) (k : UG c J) (b1 : Adj c J b b') (b2 : Adj c J b' b)
    (hb : b + b' = -1) (hf : (1 + (1 - (k.1 : Matrix β β A)) * b) * f' = 1) {ε : A} (he : ε * ε = ε) (hc : c ε = ε)
    (hm : ε • (1 - (k.1 : Matrix β β A)) = 1 - (k.1 : Matrix β β A)) (gd : UG c (dbl J))
    (hgd : (gd.1 : Matrix (β ⊕ β) (β ⊕ β) A) = fromBlocks k.1 0 0 1) :
    ∃ (s n p : UG c (dbl J)) (t : GL β A), s * s = 1 ∧ gd = s * n * s * p ∧
      (s.1 : Matrix (β ⊕ β) (β ⊕ β) A) = CC b * SS ε * Ci b ∧
      (n.1 : Matrix (β ⊕ β) (β ⊕ β) A) = CC b * fromBlocks 1 (-(f' * (1 - (k.1 : Matrix β β A)))) 0 1 * Ci b ∧
      ((n⁻¹).1 : Matrix (β ⊕ β) (β ⊕ β) A) = CC b * fromBlocks 1 (f' * (1 - (k.1 : Matrix β β A))) 0 1 * Ci b ∧
      (n.1 : Matrix (β ⊕ β) (β ⊕ β) A) * (diagCols β : Matrix (β ⊕ β) β A) = (diagCols β : Matrix (β ⊕ β) β A) * ((1 : GL β A) : Matrix β β A) ∧
      (p.1 : Matrix (β ⊕ β) (β ⊕ β) A) * (diagCols β : Matrix (β ⊕ β) β A) = (diagCols β : Matrix (β ⊕ β) β A) * (t : Matrix β β A) ∧
      (t : Matrix β β A) = 1 + b * (1 - (k.1 : Matrix β β A)) ∧ ((t⁻¹ : GL β A) : Matrix β β A) = 1 - b * (f' * (1 - (k.1 : Matrix β β A))) := by sorry
