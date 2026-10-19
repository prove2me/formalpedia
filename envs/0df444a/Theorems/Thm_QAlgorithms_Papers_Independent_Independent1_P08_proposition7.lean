-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P08_proposition7
-- name    : QAlgorithms.Papers.Independent.Independent1.P08.proposition7
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:15:49.412009+00:00
-- url     : https://prove2.me/theorems/8e57a36b-d93b-4813-a74c-a002286c5b52
-- title:
--   Proposition 7
-- statement:
--   Let $\Phi=\Phi_{t,\lambda}$ be a CPT qubit map in the fixed canonical basis, and let $T(X)=X^{\mathsf T}$. Then $T\circ\Phi\circ T$ is completely positive, and changing any individual translation coordinate $t_j$ to $-t_j$ preserves complete positivity. In addition,
--
--   $$\operatorname{CP}(\Phi\circ T)\iff\bigl[\forall j,\ \operatorname{CP}(\Phi_{t,\lambda[j\mapsto-\lambda_j]})\bigr]\iff\operatorname{CP}(T\circ\Phi).$$
--
--   Here CP denotes complete positivity. These are all three numbered assertions, together with the any-coordinate translation invariance explained immediately before the proposition.
-- source:
--   Qubit Entanglement Breaking Channels, arXiv:quant-ph/0302032v3, Proposition 7, PDF p. 10. https://arxiv.org/abs/quant-ph/0302032v3 . PDF SHA-256: dba60bd30b3ca1e23dac55f1e413d595e822e7d75c0dff71bf1b94f65337b81d.

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








































































/-- Proposition 7, PDF pp.10-11: all clauses and any-coordinate translation invariance. -/
theorem proposition7 (t lam : Bloch) (hPhi : CPT (canonical t lam)) :
    IsCompletelyPositive (transposeMap.comp ((canonical t lam).comp transposeMap)) ∧
    (∀ j, IsCompletelyPositive (canonical (Function.update t j (-t j)) lam)) ∧
    (IsCompletelyPositive ((canonical t lam).comp transposeMap) ↔
      ∀ j, IsCompletelyPositive (canonical t (Function.update lam j (-lam j)))) ∧
    (IsCompletelyPositive ((canonical t lam).comp transposeMap) ↔
      IsCompletelyPositive (transposeMap.comp (canonical t lam))) := by sorry













end QAlgorithms.Papers.Independent.Independent1.P08
