-- Prove2me | Theorems.Thm_ThreeBoundWitness_common_positive_lift
-- name    : ThreeBoundWitness.common_positive_lift
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:38:03.092732+00:00
-- url     : https://prove2.me/theorems/2fe59244-ee59-4c85-b8a5-fa6c3ae0f628
-- title:
--   One recursive stage doubles common sensitive-bit witnesses
-- statement:
--   Let a Boolean family \(F\) have a common rejected input \(z\), a common accepted input \(p\), and distinct coordinates \(e(a)\), indexed by a type \(A\), whose individual flips make every level reject \(p\). Let a recursive stage accept a pair of common accepted children at defect zero and reject whenever one of its two children is rejected at every level. For any vertex \(v\), the parent family has a common accepted input \(p'\) with an embedding
--   \[
--   e':\{\mathrm{false},\mathrm{true}\}\times A\hookrightarrow (V\times\mathrm{Bool})\times I
--   \]
--   such that flipping any coordinate \(e'(b,a)\) makes every parent level reject. This supplies the factor of two in the sensitivity witness growth.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, WitnessLifting, lines 162–185; source SHA256 3de5b42744f1a0f912bff6a7825dc8a21c88ce1eeb9e3364123000d6bca68bcc.

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Definitions.Def_Sensitivity213303_WitnessLifting

namespace OAI.Paper320
end OAI.Paper320
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ThreeBoundWitness
end ThreeBoundWitness
open ThreeBoundWitness
open OAI.Paper320
variable {L I V : Type}

theorem ThreeBoundWitness.common_positive_lift [Fintype V] {A : Type}
    (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (z p : I → Bool) (hz : ∀ l, F l z = false) (hp : ∀ l, F l p = true)
    (e : A ↪ I) (he : ∀ a l, F l (flip p {e a}) = false)
    (haccept : ∀ l x y, (∀ a, F a x = true) → (∀ a, F a y = true) →
      S.target l 0 x y = true)
    (hreject : ∀ l d x y,
      ((∀ a, F a x = false) ∨ (∀ a, F a y = false)) → S.target l d x y = false)
    (v : V) :
    ∃ (p' : ((V × Bool) × I) → Bool) (e' : (Bool × A) ↪ ((V × Bool) × I)),
      (∀ l, parent S F l p' = true) ∧
      (∀ a l, parent S F l (flip p' {e' a}) = false) := by sorry
