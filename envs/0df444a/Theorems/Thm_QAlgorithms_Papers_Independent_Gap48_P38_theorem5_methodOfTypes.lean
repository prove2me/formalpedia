-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P38_theorem5_methodOfTypes
-- name    : QAlgorithms.Papers.Independent.Gap48.P38.theorem5_methodOfTypes
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:04:53.256984+00:00
-- url     : https://prove2.me/theorems/ad7d9064-0e78-4ee6-80d4-096f72fb63b3
-- title:
--   Theorem 5 (Method of types): all simultaneous typical-projection bounds
-- statement:
--   Let $|\psi\rangle^{ABC}$ be a unit vector on three nonempty finite complex registers. Write $H(T)$ for the bit entropy of its actual marginal on $T$. There is a constant $c>0$, depending on the source but independent of $\delta$ and the requested error, with the following property. For every $\epsilon,\delta>0$, all sufficiently large positive integers $n$ admit orthogonal projections $\Pi_A,\Pi_B,\Pi_C$ on the corresponding $n$-copy registers. Put $\epsilon_n=2^{-nc\delta^2}\le\epsilon$. For each $T=A,B,C$,
--
--   $$\operatorname{Tr}[\Pi_T(\psi^T)^{\otimes n}]\ge1-\epsilon_n,\qquad 2^{nH(T)-n\delta}\le\operatorname{Tr}\Pi_T\le2^{nH(T)+n\delta}.$$
--
--   Let $|\varphi\rangle$ be the normalized, nonzero projection of $|\psi\rangle^{\otimes n}$ by $\Pi_A\otimes\Pi_B\otimes\Pi_C$. Its density matrix is within full trace norm $\epsilon_n$ of $(\psi^{ABC})^{\otimes n}$. For every $T\in\{A,B,C,AB,BC,AC\}$, its actual marginal satisfies all six bounds
--
--   $$2^{nH(T)-n\delta}\le\operatorname{rank}\varphi^{T^n}\le2^{nH(T)+n\delta},$$
--   $$2^{-nH(T)-n\delta}\le\|\varphi^{T^n}\|_2^2\le2^{-nH(T)+n\delta},\qquad 2^{-nH(T)-n\delta}\le\|\varphi^{T^n}\|_\infty\le2^{-nH(T)+n\delta}.$$
--
--   The normalized, nonzero projection by $I_A\otimes I_B\otimes\Pi_C$ alone is also within full trace norm $\epsilon_n$ of the original IID density matrix. Here $\|\cdot\|_2$ is the Hilbert–Schmidt norm and $\|\cdot\|_\infty$ the operator norm. These simultaneous bounds supply the complete typical-projection statement, rather than only a support-dimension estimate.
--
--   **Formalization Note** The stray $D$ in one projected-vector display is interpreted as trivial, consistently with the theorem's pure tripartite domain.
-- source:
--   Optimal quantum source coding with quantum information at the encoder and decoder, arXiv:0706.2907v2, PDF p. 4, Theorem 5 (Method of types): all simultaneous typical-projection bounds

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P38

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Gap48.P38

/-- Theorem 5 (method of types), PDF pp.4--5, including all lower bounds, the
C-only projection, and a delta-independent positive exponential constant.
The stray ABCD in the projected-vector display is read with D trivial, as
required by the tripartite header and every other display. -/
theorem theorem5_methodOfTypes
    (I : Fin 3 → Type) [∀ i, Fintype (I i)] [∀ i, Nonempty (I i)]
    (psi : EuclideanSpace ℂ (∀ i, I i)) (hpsi : ‖psi‖ = 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ epsilon delta : ℝ, 0 < epsilon → 0 < delta →
      ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N,
        ∃ P : (i : Fin 3) → Matrix (Restricted (fun j => Fin n → I j) {i})
          (Restricted (fun j => Fin n → I j) {i}) ℂ,
          TypicalBounds I psi n delta (Real.rpow 2 (-(n : ℝ) * c * delta ^ 2)) P ∧
          Real.rpow 2 (-(n : ℝ) * c * delta ^ 2) ≤ epsilon := by sorry

end QAlgorithms.Papers.Independent.Gap48.P38

end
