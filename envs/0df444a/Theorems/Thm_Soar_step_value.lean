-- Prove2me | Theorems.Thm_Soar_step_value
-- name    : Soar.step_value
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-22T19:01:40.131984+00:00
-- url     : https://prove2.me/theorems/bebcc985-6069-443f-ab1a-c1123804f860
-- title:
--   The expected match value of an epoch is a hindsight optimum (property (ii))
-- statement:
--   **Standing conventions.** Throughout, $\mathcal X$ (demand weight vectors) and $\mathcal Y$ (supply feature vectors) are measurable spaces, $P$ and $Q$ are probability measures on them, and the match quality function $\varphi : \mathcal X \times \mathcal Y \to \mathbb R$ is jointly measurable and bounded, $|\varphi(x,y)| \le C$ for all $x, y$. Expectations over $n$ i.i.d. demand units and $n$ independent i.i.d. supply units are integrals against the product measure $P^{\otimes n} \otimes Q^{\otimes n}$ on $\mathcal X^n \times \mathcal Y^n$. The hindsight optimum value is
--   $$U^H_n = \frac{1}{n}\,\mathbb E\Bigl[\sup_{\sigma \in S_n} \sum_{t=1}^{n} \varphi\bigl(X_t, Y_{\sigma(t)}\bigr)\Bigr],$$
--   with $S_n$ the symmetric group, and the limiting hindsight optimum is $U_\infty = \sup_{n \ge 1} U^H_n$.
--
--   Let $\mathrm{opt}$ be a measurable offline assignment solver for $\varphi$ (for every size it returns a permutation of maximum total quality). Fix $k \ge 0$. Draw the remaining supply $\tilde y = (\tilde y_0, \dots, \tilde y_k)$ i.i.d. $Q$ and, independently, the epoch randomness $(\hat x_0, (\hat x_1, \dots, \hat x_k), \sigma)$ of a SOAR epoch with $k + 1$ remaining units, and let $i$ be the index of the supply unit SOAR allocates to the arriving unit $\hat x_0$. Then the expected quality of the match made in this epoch is the hindsight optimum value of the $(k+1)$-unit problem:
--   $$\mathbb E\bigl[\varphi(\hat x_0, \tilde y_i)\bigr] = U^H_{k+1} .$$
--
--   **Role.** This is property (ii) of the proof of Theorem 1. The solver's assignment is an optimal perfect matching between an i.i.d. $P$ pool of size $k + 1$ and an i.i.d. $Q$ supply of size $k + 1$, so its total value has expectation $(k + 1)\,U^H_{k+1}$; because the true unit's slot is uniform and independent of the solved instance, the pair containing the true unit is worth, in expectation, exactly one $(k+1)$-th of the total. Summing this identity over the epochs, with the remaining supply i.i.d. at every epoch, is Theorem 1.
--
--   **Formalization Note** The expectation is over the supply and the epoch randomness jointly; measurability of the solver and of $\varphi$ and boundedness of $\varphi$ make the integrand integrable. Only the value collected in this epoch appears; the continuation is handled by the recursion of the main theorem.
-- source:
--   Y. Chen, Y. Kanoria, A. Kumar, W. Zhang, Feature-Based Dynamic Matching, SSRN working paper 4451799 (version of 27 May 2025; extended abstract in Proc. 24th ACM Conference on Economics and Computation, EC'23), https://ssrn.com/abstract=4451799, Section 3.2.2, proof of Theorem 1, property (ii)

import Mathlib
import Definitions.Def_SoarPolicy

open MeasureTheory

namespace Soar

theorem step_value {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (Q : Measure Y) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : X → Y → ℝ) (hφ : Measurable (Function.uncurry φ)) (C : ℝ) (hC : SoarBounded φ C)
    (opt : (m : ℕ) → (Fin m → X) → (Fin m → Y) → Equiv.Perm (Fin m))
    (hsolver : SoarIsSolver φ opt) (hopt : SoarSolverMeasurable opt) (k : ℕ) :
    ∫ ω : (Fin (k + 1) → Y) × SoarEpochRand X k, φ ω.2.1 (ω.1 (SoarPick opt ω.1 ω.2))
        ∂(Measure.pi fun _ : Fin (k + 1) => Q).prod (SoarEpochMeasure P k)
      = SoarHindsight P Q φ (k + 1) := by
  sorry

end Soar
