-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundGreedy_greedy_four
-- name    : Sensitivity213981Formal.ThreeBoundGreedy.greedy_four
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:31:35.011996+00:00
-- url     : https://prove2.me/theorems/813a817d-659c-4806-8db4-1ff94c56e7bd
-- title:
--   greedy four — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \prod_{\mathit{n₀}:\mathbb N} \prod_{\mathit{n₁}:\mathbb N} \prod_{\mathit{n₂}:\mathbb N} \prod_{\mathit{n₃}:\mathbb N} \prod_{\mathit{c₀}:\mathbb N} \prod_{\mathit{c₁}:\mathbb N} \prod_{\mathit{c₂}:\mathbb N} \prod_{\mathit{c₃}:\mathbb N} \prod_{\mathit{a₀}:\mathbb N} \prod_{\mathit{a₁}:\mathbb N} \prod_{\mathit{a₂}:\mathbb N} \prod_{\mathit{a₃}:\mathbb N} \left(\bigl(\mathit{n₀} \le \mathit{c₀}\bigr)\to \left(\bigl(\bigl(\mathit{n₀}+\mathit{n₁}\bigr) \le \mathit{c₁}\bigr)\to \left(\bigl(\bigl(\bigl(\mathit{n₀}+\mathit{n₁}\bigr)+\mathit{n₂}\bigr) \le \mathit{c₂}\bigr)\to \prod_{\mathit{h₃}:\bigl(\bigl(\bigl(\bigl(\mathit{n₀}+\mathit{n₁}\bigr)+\mathit{n₂}\bigr)+\mathit{n₃}\bigr) \le \mathit{c₃}\bigr)} \prod_{\mathit{ha₀}:\bigl(\mathit{a₁} \le \mathit{a₀}\bigr)} \prod_{\mathit{ha₁}:\bigl(\mathit{a₂} \le \mathit{a₁}\bigr)} \prod_{\mathit{ha₂}:\bigl(\mathit{a₃} \le \mathit{a₂}\bigr)} \left(\text{let }\mathit{g₀}=\operatorname{Min.min}\bigl(\mathit{c₀}, \operatorname{Min.min}\bigl(\mathit{c₁}, \operatorname{Min.min}\bigl(\mathit{c₂}, \mathit{c₃}\bigr)\bigr)\bigr)\text{ in }\left(\text{let }\mathit{g₁}=\bigl(\operatorname{Min.min}\bigl(\mathit{c₁}, \operatorname{Min.min}\bigl(\mathit{c₂}, \mathit{c₃}\bigr)\bigr)-\mathit{g₀}\bigr)\text{ in }\left(\text{let }\mathit{g₂}=\bigl(\operatorname{Min.min}\bigl(\mathit{c₂}, \mathit{c₃}\bigr)-\bigl(\mathit{g₀}+\mathit{g₁}\bigr)\bigr)\text{ in }\left(\text{let }\mathit{g₃}=\bigl(\mathit{c₃}-\bigl(\bigl(\mathit{g₀}+\mathit{g₁}\bigr)+\mathit{g₂}\bigr)\bigr)\text{ in }\bigl(\bigl(\bigl(\bigl(\bigl(\mathit{n₀}\cdot \mathit{a₀}\bigr)+\bigl(\mathit{n₁}\cdot \mathit{a₁}\bigr)\bigr)+\bigl(\mathit{n₂}\cdot \mathit{a₂}\bigr)\bigr)+\bigl(\mathit{n₃}\cdot \mathit{a₃}\bigr)\bigr) \le \bigl(\bigl(\bigl(\bigl(\mathit{g₀}\cdot \mathit{a₀}\bigr)+\bigl(\mathit{g₁}\cdot \mathit{a₁}\bigr)\bigr)+\bigl(\mathit{g₂}\cdot \mathit{a₂}\bigr)\bigr)+\bigl(\mathit{g₃}\cdot \mathit{a₃}\bigr)\bigr)\bigr)\right)\right)\right)\right)\right)\right)\right)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding greedy four step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; PrefixGreedy.lean, lines 95–121.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundGreedy.greedy_four :
∀ (n₀ n₁ n₂ n₃ c₀ c₁ c₂ c₃ a₀ a₁ a₂ a₃ : Nat) (h₀ : @LE.le.{0} Nat instLENat n₀ c₀)
  (h₁ : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n₀ n₁) c₁)
  (h₂ :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n₀ n₁) n₂)
      c₂)
  (h₃ :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n₀ n₁) n₂)
        n₃)
      c₃)
  (ha₀ : @LE.le.{0} Nat instLENat a₁ a₀) (ha₁ : @LE.le.{0} Nat instLENat a₂ a₁) (ha₂ : @LE.le.{0} Nat instLENat a₃ a₂),
  have g₀ : Nat := @Min.min.{0} Nat instMinNat c₀ (@Min.min.{0} Nat instMinNat c₁ (@Min.min.{0} Nat instMinNat c₂ c₃));
  have g₁ : Nat :=
    @HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
      (@Min.min.{0} Nat instMinNat c₁ (@Min.min.{0} Nat instMinNat c₂ c₃)) g₀;
  have g₂ : Nat :=
    @HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (@Min.min.{0} Nat instMinNat c₂ c₃)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g₀ g₁);
  have g₃ : Nat :=
    @HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) c₃
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g₀ g₁) g₂);
  @LE.le.{0} Nat instLENat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n₀ a₀)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n₁ a₁))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n₂ a₂))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n₃ a₃))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) g₀ a₀)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) g₁ a₁))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) g₂ a₂))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) g₃ a₃)) := by sorry
