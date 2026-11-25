-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__mass_pow_le_exp_rpow_18515efb5c9a
-- name    : P2M_Formalism_MainNotions_BridgeLemma__mass_pow_le_exp_rpow_18515efb5c9a
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:59:23.895339+00:00
-- url     : https://prove2.me/theorems/2aa35c03-e57a-4d24-956d-038947c898e5
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  mass pow le exp rpow 18515efb5c9a: P2 M Formalism Main Notions Bridge Lemma  mass pow le exp rpow 18515efb5c9a
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  mass pow le exp rpow 18515efb5c9a construction uses the P2 M Formalism Main Notions Bridge Lemma  mass pow le exp rpow 18515efb5c9a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/MassPowLeExpRpow.lean#L16-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/MassPowLeExpRpow.lean#L16-L84

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_MassPowLeExpRpow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂

theorem P2M_Formalism_MainNotions_BridgeLemma__mass_pow_le_exp_rpow_18515efb5c9a (f m : ℕ) (rd L B₁ C κ : ℝ) (hf : 1 ≤ f) (hm : 2 ≤ m) (hrd : 2 ≤ rd) (hL : 1 ≤ L) (hκ : 1 ≤ κ)
    (hlf : Real.log f ≤ m) (hlrd : Real.log rd ≤ κ * L) (hB0 : 0 ≤ B₁) (hB : B₁ ≤ 4 * f * rd) (hC : 55 * κ ≤ C ^ 2) :
    (1 + 2 * B₁) ^ (2 * (2 * f)) * (1 + 2 * (B₁ * rd)) ^ (2 * (2 * f)) * (B₁ * (B₁ * rd)) ^ (4 * (2 * f)) ≤
      (Real.exp L ^ (C * (m : ℝ) ^ 2 * f)) ^ C := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«mass_pow_le_exp_rpow» := P2M_Formalism_MainNotions_BridgeLemma__mass_pow_le_exp_rpow_18515efb5c9a
