-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P24_haarTwirl_preservesOptimum
-- name    : QAlgorithms.Papers.Independent.Next46.P24.haarTwirl_preservesOptimum
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:55:40.428419+00:00
-- url     : https://prove2.me/theorems/5c2f0bbd-5456-4f47-b934-60a9ddfa8fbd
-- title:
--   Lemma 1 and Eq.(8): Haar averaging preserves the optimum and yields covariance
-- statement:
--   Fix an integer $d\ge2$. All four wires $3,2,1,0$ are copies of $\mathbb C^d$, with the same fixed orthonormal coordinate bases. A feasible fixed network is a positive operator $C$ on their ordered tensor product satisfying $\operatorname{Tr}_3 C=I_2\otimes C^{(1)}$ and $\operatorname{Tr}_1 C^{(1)}=I_0$. For $U\in SU(d)$ put $v_U=|U^\dagger\rangle\!\rangle_{30}\otimes|U^*\rangle\!\rangle_{21}$, transported to wire order $3210$, and define the average channel Choi-state fidelity by
--
--   $$
--   \overline F(C)=\frac1{d^2}\int_{SU(d)}\langle v_U|C|v_U\rangle\,dU.
--   $$
--
--   Both group integrals use normalized Haar probability measure. Define $R(U,W)=U_3\otimes W_2\otimes U_1\otimes W_0$ and the concrete twirl
--
--   $$
--   \widetilde C=\int_{SU(d)\times SU(d)}R(U,W)C R(U,W)^\dagger\,dU\,dW.
--   $$
--
--   The twirl kernel and the fidelity integrand are integrable; $\widetilde C$ is feasible, commutes with every $R(U,W)$, and satisfies $\overline F(\widetilde C)=\overline F(C)$. Consequently, if $C$ is a maximizer among all feasible combs, its twirl is also a maximizer. This makes covariance available without changing the optimization problem.
--
--   **Formalization Note** The printed quantified $V$ in Eq. (8) is read as $U$, consistently with its displayed operator and averaging proof.
-- source:
--   Minimal computational-space implementation of multi-round quantum protocols, arXiv:1006.1780v1, PDF p. 3, Lemma 1 and Eq.(8): Haar averaging preserves the optimum and yields covariance

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P24

noncomputable section

open MeasureTheory TopologicalSpace

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Next46.P24

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P24.combContinuousENorm

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P24.pairContinuousENorm

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P24.wireContinuousENorm

/-- PDF p.3, Lemma 1 and its averaging proof. Printed quantified V is changed to U,
as required by the displayed action and the proof. Integrability is a conclusion. -/
theorem haarTwirl_preservesOptimum (d : ℕ) (hd : 2 ≤ d)
    (C : CombMatrix d) (hC : IsInversionComb C) :
    Integrable (twirlKernel C) ((haar d).prod (haar d)) ∧
    Integrable (inversionFidelity C) (haar d) ∧
    IsInversionComb (inversionTwirl C) ∧ InversionCovariant (inversionTwirl C) ∧
    inversionAverage (inversionTwirl C) = inversionAverage C ∧
    (Optimal C → Optimal (inversionTwirl C)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P24

end
