-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_backgroundAntisymmetricExample
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.backgroundAntisymmetricExample
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T19:40:16.094992+00:00
-- url     : https://prove2.me/theorems/d9a85646-f877-4fb7-84f5-197741d680e0
-- title:
--   Antisymmetric states separate small entanglement from separable distance
-- statement:
--   For $d\ge2$, let $\alpha_d=(\mathrm{id}-\mathrm{SWAP})/[d(d-1)]$ be the normalized totally antisymmetric state on $\mathbb C^d\otimes\mathbb C^d$. There are constants $K>0$ and $N\ge2$ such that
--
--   $$E_{\rm sq}(\alpha_d)\le K/d\quad(d\ge N),\qquad \inf_{\sigma\in\mathcal S}\Delta(\alpha_d,\sigma)\ge\tfrac14\quad(d\ge2).$$
--
--   The constants precede the dimension, and the state is computed from the swap operator. This is the example used on p.28 to explain why the quantitative faithfulness estimate needs a dimension factor.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 28, BackgroundAntisymmetricExample

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12

noncomputable section

open Filter MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P12

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP matrixPower permute)

open QAlgorithms.Papers.Independent.Information100.P80 (OperatorLE groupedPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

/-- Antisymmetric example (PDF p.28): O(1/d) entanglement but distance >=1/4.
The universal constants precede d, and the state is computed rather than assumed. -/
theorem backgroundAntisymmetricExample :
    (∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ d : ℕ, N ≤ d →
      squashedEntanglement (antisymmetricState d) ≤ K / (d : ℝ)) ∧
    (∀ (d : ℕ) (hd : 2 ≤ d),
      letI : Nonempty (Fin d) := ⟨⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hd⟩⟩
      separableDistance (antisymmetricState d) ≥ 1/4) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
