-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P37_binomial_emission_statistics
-- name    : QAlgorithms.Papers.Independent.Intake100.P37.binomial_emission_statistics
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:12:10.019778+00:00
-- url     : https://prove2.me/theorems/8ede6c0a-a86d-4d1c-975f-e8db80332062
-- title:
--   Binomial emission law, short-time order, and mean emitted count
-- statement:
--   In the leading (B1) model, fix $A\ge0$, $m\ge1$, and real $\gamma$. Let $p_l(t)$ be the squared modulus of the actual exponential coefficient for $0\le l\le A$, and put $q(t)=\sin^2(\gamma\sqrt m\,t)$. For all real $t$,
--
--   $$
--   p_l(t)=\binom Al\cos^{2(A-l)}(\gamma\sqrt m\,t)\sin^{2l}(\gamma\sqrt m\,t)
--   =\binom Al(1-q(t))^{A-l}q(t)^l.
--   $$
--
--   These probabilities sum to one, their mean additional emitted photon count is $\sum_llp_l(t)=Aq(t)$, and for every fixed $l$, $p_l(t)=O(t^{2l})$ as $t\to0$. The total photon-count mean is therefore $m+Aq(t)$. Exponent zero is interpreted as one, including at zero trigonometric factors. In particular $l=0$ has order $O(1)$ and $A=0$ is the unit mass at zero emission. This binomial law concerns the leading approximation, not the exact finite-$m$ physical Hamiltonian.
-- source:
--   Lambda's, V's and optimal cloning with stimulated emission, arXiv:quant-ph/0003025v1, PDF p. 10, Appendix B, Eq.(B3) and following paragraph

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P37

open QAlgorithms

open scoped Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.10 Eq.(B3) and following paragraph: binomial emission statistics,
short-time order t^(2l), and mean ADDITIONAL photon count, only in the B1 model.
Natural exponent zero has value one, including A=l=0. -/
theorem binomial_emission_statistics (A m : ℕ) (hm : 1 ≤ m) (gamma : ℝ) :
    (∀ t : ℝ, ∀ l : Fin (A + 1),
      leadingProbability A m gamma t l =
        (Nat.choose A l.val : ℝ) * Real.cos (gamma * Real.sqrt m * t) ^ (2 * (A - l.val)) *
          Real.sin (gamma * Real.sqrt m * t) ^ (2 * l.val) ∧
      leadingProbability A m gamma t l =
        (Nat.choose A l.val : ℝ) *
          (1 - Real.sin (gamma * Real.sqrt m * t) ^ 2) ^ (A - l.val) *
          (Real.sin (gamma * Real.sqrt m * t) ^ 2) ^ l.val) ∧
    (∀ t : ℝ, (∑ l : Fin (A + 1), leadingProbability A m gamma t l) = 1 ∧
      (∑ l : Fin (A + 1), (l.val : ℝ) * leadingProbability A m gamma t l) =
        A * Real.sin (gamma * Real.sqrt m * t) ^ 2) ∧
    (∀ l : Fin (A + 1),
      Asymptotics.IsBigO (nhds (0 : ℝ))
        (fun t : ℝ => leadingProbability A m gamma t l)
        (fun t : ℝ => t ^ (2 * l.val))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P37

end
