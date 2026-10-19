-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P08_axialCriterion
-- name    : QAlgorithms.Papers.Independent.Independent1.P08.axialCriterion
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:17:40.21557+00:00
-- url     : https://prove2.me/theorems/8c7b2663-1674-416a-afc8-71aeefb940ab
-- title:
--   Equation 29 axial-translation EBT criterion
-- statement:
--   For a CPT canonical qubit map with $t=(0,0,t_3)$,
--
--   $$\Phi_{t,\lambda}\text{ is EBT}\iff (|\lambda_1|+|\lambda_2|)^2\le(1-|\lambda_3|)^2-t_3^2.$$
--
--   For fixed $t_3,l_3$ with $|l_3|\le1$ and $q=(1-|l_3|)^2-t_3^2\ge0$, its EBT slice is exactly $\{(v_1,v_2):|v_1|+|v_2|\le\sqrt q\}$. This includes the filled square and its collapsed endpoints; a negative radicand is not totalized into an extra radius-zero slice.
-- source:
--   Qubit Entanglement Breaking Channels, arXiv:quant-ph/0302032v3, Equation 29 axial-translation EBT criterion, PDF p. 16. https://arxiv.org/abs/quant-ph/0302032v3 . PDF SHA-256: dba60bd30b3ca1e23dac55f1e413d595e822e7d75c0dff71bf1b94f65337b81d.

import Definitions.Def_QAlgorithms_Defs_QubitBlochMaps
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P08_Model
set_option autoImplicit false

/-! Ruskai, Qubit Entanglement Breaking Channels, arXiv:quant-ph/0302032v3.
All locators are PDF pages. Convexity is real; ambiguous claims are in HARD.md. -/

noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P08

open QAlgorithms.Entanglement QAlgorithms.QubitChannels


















































































/-- Equation (29), PDF p.16: CPT retained. Disk formula has |lambda3|≤1 and
nonnegative radicand, avoiding the spurious large-|lambda3| branch. -/
theorem axialCriterion :
    (∀ t3 : ℝ, ∀ lam : Bloch, CPT (canonical ![0,0,t3] lam) →
      (EBT (canonical ![0,0,t3] lam) ↔
        (|lam 0|+|lam 1|)^2 ≤ (1-|lam 2|)^2-t3^2)) ∧
    (∀ t3 l3 : ℝ, |l3| ≤ 1 → 0 ≤ (1-|l3|)^2-t3^2 →
      {v : Fin 2 → ℝ | EBT (canonical ![0,0,t3] ![v 0,v 1,l3])} =
        {v | |v 0|+|v 1| ≤ Real.sqrt ((1-|l3|)^2-t3^2)}) := by sorry



end QAlgorithms.Papers.Independent.Independent1.P08
