-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_regularized_approximants
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.regularized_approximants
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:27:20.354968+00:00
-- url     : https://prove2.me/theorems/cf8f272e-198b-40be-9d3d-4abcd19d4567
-- title:
--   Remark 6.5: choice of approximants and continuous representatives
-- statement:
--   Let $M$ be a nonempty compact metric space with its Borel sigma-algebra, and let $\varphi:M\to M$ be continuous. Write $\mathcal P(M)$ for Borel probabilities with the weak topology, $\mathcal P_\varphi(M)$ for invariant probabilities, and $\mathcal E_\varphi(M)$ for ergodic probabilities. Entropy $h_\varphi$ is Kolmogorov–Sinai entropy with natural logarithms. For a bounded Borel sequence $\mathcal G=(G_n)_{n\ge1}$, asymptotic additivity means uniform approximation at linear scale by sums $S_n g=\sum_{j=0}^{n-1}g\circ\varphi^j$ of continuous functions. For such a sequence, $\mathcal G(Q)$ denotes the constructed real limit of $n^{-1}\int G_n\,dQ$ on invariant probabilities, and $p(\mathcal G)$ denotes its topological pressure. All time limits use positive integers.
--
--   Let $\mathcal G\in\mathcal A(M)$. If every $G_n$ is continuous, $f_k=G_k/k$ is a continuous approximating family, uniformly bounded in supremum norm. In general one can choose continuous approximants $f_k$ with
--   $$\sup_{k\ge1}\|f_k\|_\infty<\infty,\qquad\|G_k/k-f_k\|_\infty\to0.$$
--   There also exists an equivalent AA sequence $\mathcal H=(H_n)$ with every $H_n$ continuous, so $\|G_n-H_n\|_\infty/n\to0$. The uniform bound concerns this choice of regularized approximants, not all possible approximating families. This supplies continuous representatives within the source equivalence class.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 43, Remark 6.5: choice of approximants and continuous representatives

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P82

noncomputable section

open Filter MeasureTheory Set

open scoped Topology BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P82

attribute [local instance] Classical.propDecidable

section CompactDynamics

variable {M : Type*} [instMetric : MetricSpace M] [instCompact : CompactSpace M]
  [instNonempty : Nonempty M] [instMeasurable : MeasurableSpace M] [instBorel : BorelSpace M]

-- Retain standing assumptions even when a displayed lemma does not use them.

include instCompact instNonempty instBorel

local instance : DecidableEq M := Classical.decEq M

/-- Remark 6.5, arXiv:1712.05167v3, PDF p.43. Continuous block approximants,
uniformly bounded regularized approximants, and an equivalent continuous AA
sequence. The bound is existential for this choice, not universal over all families. -/
theorem regularized_approximants (phi : M → M) (hphi : Continuous phi)
    (G : ℕ → M → ℝ) (hG : AsymptoticallyAdditive phi G) :
    ((∀ n : ℕ, 1 ≤ n → Continuous (G n)) →
      ApproximatingFamily phi G (fun k x => G k x / (k : ℝ)) ∧
      ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k → supNorm (fun x => G k x / (k : ℝ)) ≤ C) ∧
    (∃ F : ℕ → M → ℝ, ApproximatingFamily phi G F ∧
      (∃ C : ℝ, ∀ k : ℕ, 1 ≤ k → supNorm (F k) ≤ C) ∧
      Tendsto (fun k : ℕ => supNorm (fun x =>
        G (k + 1) x / ((k + 1 : ℕ) : ℝ) - F (k + 1) x)) atTop (𝓝 0)) ∧
    (∃ H : ℕ → M → ℝ, AsymptoticallyAdditive phi H ∧
      (∀ n : ℕ, 1 ≤ n → Continuous (H n)) ∧ EquivalentPotentials G H) := by sorry

end CompactDynamics

end QAlgorithms.Papers.Independent.Intake100.P82

end
