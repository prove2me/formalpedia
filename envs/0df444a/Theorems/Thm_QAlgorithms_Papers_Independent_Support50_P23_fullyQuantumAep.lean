-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P23_fullyQuantumAep
-- name    : QAlgorithms.Papers.Independent.Support50.P23.fullyQuantumAep
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:56:03.832+00:00
-- url     : https://prove2.me/theorems/149f5afb-7faa-4cc4-8005-62e5568d8a44
-- title:
--   Fully quantum asymptotic equipartition property
-- statement:
--   Let $\rho_{AB}$ be a normalized state on arbitrary finite-dimensional nonzero complex Hilbert spaces $A$ and $B$. Use binary entropies and smooth over subnormalized states at sine distance at most $\varepsilon$, where sine distance is $\sqrt{1-F^2}$ and $F$ is root fidelity. For every $0<\varepsilon<1$, both positive-integer copy-count limits below exist as finite real numbers, and
--   $$
--   \lim_{\varepsilon\downarrow0}\lim_{n\to\infty}\frac{H_{\min}^{\varepsilon}(A^n|B^n)_{\rho^{\otimes n}}}{n}
--   =H(A|B)_\rho
--   =\lim_{\varepsilon\downarrow0}\lim_{n\to\infty}\frac{H_{\max}^{\varepsilon}(A^n|B^n)_{\rho^{\otimes n}}}{n}.
--   $$
--   Here $H(A|B)_\rho=S(\rho_{AB})-S(\rho_B)$ and $\rho_B=\operatorname{tr}_A\rho_{AB}$. The existential real functions in the statement witness the inner limits; outer convergence is through $(0,1)$. This is the paper's first-order i.i.d. entropy limit.
-- source:
--   A Fully Quantum Asymptotic Equipartition Property, arXiv:0811.1221v3, PDF p. 2, Theorem 1 (AEP), equations (6)-(7); original paper-level seed

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P23

noncomputable section

open Filter

open scoped ENNReal ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Support50.P23

attribute [local instance] Classical.propDecidable

-- Exact accepted bodies. Other similarly named catalogue entries use different
-- smoothing, conditioning order, logarithm base, or channel-level objects.

open QAlgorithms.Papers.Independent.Gap20.P03 (fixedMin)

open QAlgorithms.Papers.Independent.Dependency50.P36 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized)

open QAlgorithms.Papers.Independent.Information100.P69 (matrixPower)

variable {A B C D I : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype I]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D] [DecidableEq I]

/-- Theorem 1, PDF p.2, (6)-(7), proved on p.6. Both iterated limits include
existence of the inner limits; n+1 ranges over positive copy counts. -/
theorem fullyQuantumAep [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho) :
    ∃ lower upper : ℝ → ℝ,
      (∀ epsilon ∈ Set.Ioo (0 : ℝ) 1,
        Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)⁻¹ : EReal) *
          sineSmoothMin (jointPower rho (n + 1)) epsilon) atTop (nhds (lower epsilon : EReal)) ∧
        Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)⁻¹ : EReal) *
          sineSmoothMax (jointPower rho (n + 1)) epsilon) atTop (nhds (upper epsilon : EReal))) ∧
      Tendsto lower (nhdsWithin 0 (Set.Ioo 0 1)) (nhds (conditionalEntropyBitsAB rho)) ∧
      Tendsto upper (nhdsWithin 0 (Set.Ioo 0 1)) (nhds (conditionalEntropyBitsAB rho)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P23

end
