-- Prove2me | Theorems.Thm_VdNSim_Sparse_theorem_1
-- name    : VdNSim.Sparse.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:32:02.730454+00:00
-- url     : https://prove2.me/theorems/b591cbb2-660b-4f97-8e5a-76740e63c4af
-- title:
--   Theorem 1, p. 2 — sampling simulation when U†OU is sparse
-- statement:
--   Let $\psi$ be a normalized $n$-qubit state, let $U$ be unitary, and let $O$ be a Hermitian observable of spectral norm at most one. Suppose $B=U^\dagger O U$ is $s$-sparse and supplied with column data. Using $K\ge1$ samples from the Born law of $\psi$ for each of the paper's two sampling functions, form its estimator $\widehat o$. For every $\varepsilon>0$,
--
--   $$\Pr\{|\widehat o-\langle U\psi|O|U\psi\rangle|>\varepsilon\}\le8s\exp\!\left(-\frac{K\varepsilon^2}{32s^4}\right).$$
--
--   This gives the accuracy guarantee behind Theorem 1's classical simulation claim: the output observable's expectation can be recovered from samples and sparse column data.
--
--   **Formalization Note** This is the paper's explicit estimator, so it cannot inspect the target expectation directly. The finite statement grants sampling and coefficient access associated with CT states and column access associated with ECS operators, but does not assert their polynomial running times or a uniform circuit family. The displayed constant is derived from Theorem 3's proof and Eq. (18), rather than printed in Theorem 1.
-- source:
--   Van den Nest, Simulating quantum computers with probabilistic methods, arXiv:0911.1624v3, p. 2, Theorem 1; p. 11, Theorem 3; pp. 12–13, proof; p. 23, Eq. (18)

import Mathlib
import Definitions.Def_VdNSim_Sparse_Model

noncomputable section
open scoped Matrix

namespace VdNSim.Sparse

/-- Theorem 1, p. 2, as the explicit accuracy guarantee of the paper's estimator. -/
theorem theorem_1 {n s K : ℕ} (hK : 0 < K)
    (ψ : Bits n → ℂ) (hψ : ∑ x, prob ψ x = 1)
    (U : Matrix.unitaryGroup (Bits n) ℂ)
    (O : Matrix (Bits n) (Bits n) ℂ)
    (hO : O.IsHermitian) (hO1 : QAlgorithms.specNorm O ≤ 1)
    (hsp : IsSparse s (Matrix.conjTranspose (U : Matrix (Bits n) (Bits n) ℂ) * O *
      (U : Matrix (Bits n) (Bits n) ℂ)))
    (D : ColumnData (Matrix.conjTranspose (U : Matrix (Bits n) (Bits n) ℂ) * O *
      (U : Matrix (Bits n) (Bits n) ℂ)) s)
    {ε : ℝ} (hε : 0 < ε) :
    failProb ψ ψ D K
      (matElem ((U : Matrix (Bits n) (Bits n) ℂ) *ᵥ ψ) O
        ((U : Matrix (Bits n) (Bits n) ℂ) *ᵥ ψ)) ε ≤
      8 * (s : ℝ) * Real.exp (-((K : ℝ) * ε ^ 2) / (32 * (s : ℝ) ^ 4)) := by sorry

end VdNSim.Sparse
