-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P15_iid_reference_fidelity_estimate
-- name    : QAlgorithms.Papers.Independent.Extend50.P15.iid_reference_fidelity_estimate
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:59:21.803904+00:00
-- url     : https://prove2.me/theorems/25995979-b963-4656-8d8e-a72a8fb088a0
-- title:
--   Explicit asymptotic fidelity estimate for surviving Bell references
-- statement:
--   Fix $d\ge2$, $\beta>0$ and $\gamma\in(0,1)$. For an integer total-size parameter $n$, let $n_C=\lfloor n^\gamma\rfloor$. Consider a positive integer survivor count $s$ satisfying $s=\beta n$. For each size-$s$ Young diagram $\lambda$ of height at most $d$, set $\widetilde\lambda_i=\lambda_i+d-i$ and
--
--   $$p_{\lambda,s}=\frac{s!\prod_{i<j}(\widetilde\lambda_i-\widetilde\lambda_j)^2}{d^s\prod_{i=1}^d\widetilde\lambda_i!\prod_{k=1}^{d-1}k!}.$$
--
--   Use the canonical A12 estimate density determined by this normalized integer Schur--Weyl law. Let $F_s$ be the stabilized squared fidelity of its averaged $U^{\otimes n_C}\otimes\overline U$ channel relative to the identity, and set $\Gamma=d^{d(d-1)/2}/\prod_{k=1}^{d-1}k!$. For every $\alpha>0$ there is $N\ge1$, fixed before $n$ and $s$, such that for all $n\ge N$ and positive integer $s=\beta n$,
--
--   $$1-F_s\le\frac{(d^2-d+32)\Gamma}{\beta^2}\left(\frac1{2s}\right)^{1-\alpha-2\gamma}.$$
--
--   This is the analytical reference-fidelity estimate used in Theorem 2. It uses no half-integer Young shapes. The source's exact ratio condition restricts the admitted integer pairs; it does not assert an integer survivor count for every real $\beta$ and every $n$.
-- source:
--   Optimal Universal Quantum Error Correction via Bounded Reference Frames, arXiv:2007.09154v2, PDF p. 25, C6--C8

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P15

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P15

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

open QAlgorithms.Papers.Independent.Information100.P75 (Register)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- C8, PDF pp.25--29: the well-defined analytical reference-fidelity estimate.
L enumerates ALL size-s Young diagrams, not an arbitrary selected support. The
relation s=beta*n is retained literally; only integer pairs satisfying it are claimed.
Gamma is fixed before alpha and the asymptotic threshold. No half-integer-shape
objects from the proof occur in this signature. -/
theorem iid_reference_fidelity_estimate (d : ℕ) (hd : 2 ≤ d)
    (mu : Measure (Matrix.specialUnitaryGroup (Fin d) ℂ)) (hmu : IsNormalizedHaar mu)
    (L : (s : ℕ) → Finset (QAlgorithms.Schur.Partition d s))
    (hL : ∀ s (lambda : QAlgorithms.Schur.Partition d s), lambda ∈ L s)
    (beta gamma : ℝ) (hbeta : 0 < beta) (hgamma : 0 < gamma) (hgammaOne : gamma < 1) :
    ∀ alpha : ℝ, 0 < alpha → ∃ N : ℕ, 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n → ∀ s : ℕ, 1 ≤ s → (s : ℝ) = beta * n →
        1 - worstFidelity
          (referenceCostChannel mu (computationSize gamma n) (L s) schurWeylMass) id ≤
          (((d : ℝ) ^ 2 - d + 32) * schurWeylConstant d / beta ^ 2) *
            (1 / (2 * (s : ℝ))) ^ (1 - alpha - 2 * gamma) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P15

end
