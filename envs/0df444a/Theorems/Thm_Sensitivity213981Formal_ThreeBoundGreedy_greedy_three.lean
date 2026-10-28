-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundGreedy_greedy_three
-- name    : Sensitivity213981Formal.ThreeBoundGreedy.greedy_three
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:30:51.712988+00:00
-- url     : https://prove2.me/theorems/79fdf24e-7c30-4772-84c9-9501243d3014
-- title:
--   Optimal three-tier filling under prefix capacities
-- statement:
--   Let \(n_0,n_1,n_2,c_0,c_1,c_2,a_0,a_1,a_2\) be natural numbers with \(a_0\ge a_1\ge a_2\), and assume
--   \[
--   n_0\le c_0,\quad n_0+n_1\le c_1,\quad n_0+n_1+n_2\le c_2.
--   \]
--   Define \(g_0=\min(c_0,c_1,c_2)\), \(g_1=\min(c_1,c_2)-g_0\), and \(g_2=c_2-g_0-g_1\). Then
--   \[
--   n_0a_0+n_1a_1+n_2a_2\le g_0a_0+g_1a_1+g_2a_2.
--   \]
--   Thus the largest weights may be filled first after replacing the capacities by their suffix minima. This bounds the weighted contribution of the three negative-candidate tiers.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; PrefixGreedy.lean, lines 74–93.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundGreedy.greedy_three :
∀ (n₀ n₁ n₂ c₀ c₁ c₂ a₀ a₁ a₂ : Nat) (h₀ : @LE.le.{0} Nat instLENat n₀ c₀)
  (h₁ : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n₀ n₁) c₁)
  (h₂ :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n₀ n₁) n₂)
      c₂)
  (ha₀ : @LE.le.{0} Nat instLENat a₁ a₀) (ha₁ : @LE.le.{0} Nat instLENat a₂ a₁),
  have g₀ : Nat := @Min.min.{0} Nat instMinNat c₀ (@Min.min.{0} Nat instMinNat c₁ c₂);
  have g₁ : Nat :=
    @HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (@Min.min.{0} Nat instMinNat c₁ c₂) g₀;
  have g₂ : Nat :=
    @HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) c₂
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g₀ g₁);
  @LE.le.{0} Nat instLENat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n₀ a₀)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n₁ a₁))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n₂ a₂))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) g₀ a₀)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) g₁ a₁))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) g₂ a₂)) := by sorry
