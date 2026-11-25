-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_leibniz_ofFn
-- name    : ReciprocityTheory.PGsh.leibniz_ofFn
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:09:03.39975+00:00
-- url     : https://prove2.me/theorems/e1179ac0-51d2-5ad6-b475-2d6a5565527e
-- title:
--   PGsh: leibniz of Fn
-- statement:
--   The PGsh construction uses the leibniz of Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L34-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L34-L52

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

theorem ReciprocityTheory.PGsh.leibniz_ofFn {m s : ℕ} (ds : Fin m → Derivation R A A) (P : Fin s → A) :
    (List.ofFn fun i => (ds i : A →ₗ[R] A)).prod (∏ k, P k) =
      ∑ φ : Fin m → Fin s,
        ∏ k, (List.ofFn fun i => if φ i = k then (ds i : A →ₗ[R] A) else 1).prod (P k) := by sorry
