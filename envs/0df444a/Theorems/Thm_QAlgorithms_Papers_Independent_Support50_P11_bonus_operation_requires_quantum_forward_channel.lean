-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P11_bonus_operation_requires_quantum_forward_channel
-- name    : QAlgorithms.Papers.Independent.Support50.P11.bonus_operation_requires_quantum_forward_channel
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:15:58.911761+00:00
-- url     : https://prove2.me/theorems/8c471953-35b4-41d7-8524-80ad575bbf75
-- title:
--   §VII.C, Fig.7: a PPT and NS operation requiring quantum forward assistance
-- statement:
--   Define a two-qubit-input bipartite operation $\mathcal Z$ as follows. Bob measures his input in the computational basis to obtain $b$, chooses an independent uniform bit $r$, and outputs $r$. Alice measures her input in the computational basis when $b=0$ and the Hadamard basis when $b=1$, obtains $a$, and outputs $a\oplus r$. Then $\mathcal Z$ is CPTP, PPT-preserving and non-signalling in both directions. For every exact forward realization of this fixed operation using positive finite side registers, CPTP encoder $E$, side channel $F$ and decoder $D$,
--   $$\mathcal Z=(\operatorname{id}\otimes D)\circ(\operatorname{id}\otimes F\otimes\operatorname{id})\circ(E\otimes\operatorname{id}),$$
--   with the tensor reordering specified in the definition, there exist CPTP maps $E_0,D_0$ with
--   $$D_0\circ F\circ E_0=\operatorname{id}_2.$$
--   In particular $F$ cannot be Horodecki. This is the separately defined operation of Fig.7, with a conclusion quantified over every exact forward implementation.
-- source:
--   On the power of PPT-preserving and non-signalling codes, arXiv:1406.7142v2, PDF p. 12, §VII.C, Fig.7: a PPT and NS operation requiring quantum forward assistance

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P11

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P11

open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing permutationMatrix)

open QAlgorithms.Papers.Independent.Information100.P21 (pt)

open QAlgorithms.Papers.Independent.Dependency50.P09 (tensorAction)

open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)

open QAlgorithms.Papers.Independent.Information100.P69 (replacer)

open QAlgorithms.Papers.Independent.Gap20.P19 (wernerIsometry)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF pp.12--13, section VII.C, Fig.7: this independently defined CPTP, PPT,
non-signalling operation forces every exact forward side channel to transmit a qubit
perfectly. This conclusion is not asserted for the different operation of Example 9. -/
theorem bonus_operation_requires_quantum_forward_channel :
    IsChannel bonusOperation ∧ NSBA bonusOperation ∧ NSAB bonusOperation ∧ PPTMap bonusOperation ∧
    ∀ q r : ℕ, 0 < q → 0 < r →
    ∀ E : Superop (Fin 2) (Fin 2 × Fin q),
    ∀ F : Superop (Fin q) (Fin r), ∀ D : Superop (Fin r × Fin 2) (Fin 2),
      IsChannel E → IsChannel F → IsChannel D → forwardOp E F D = bonusOperation →
        PerfectQubit F ∧ ¬ Horodecki F := by sorry

end QAlgorithms.Papers.Independent.Support50.P11

end
