-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P09_continuousPurifications
-- name    : QAlgorithms.Papers.Independent.Frontier18.P09.continuousPurifications
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:59:52.502254+00:00
-- url     : https://prove2.me/theorems/068ccf92-42a1-4e34-9c59-176f8f1d22c3
-- title:
--   Continuous choice of purifications with a prescribed limiting purification
-- statement:
--   Let $\mathcal H$ and $\mathcal K$ be nonzero separable complex Hilbert spaces with equal Hilbert dimensions. Let $\omega_0$ be a pure density operator on their completed tensor product. If a sequence of density operators $\rho_k$ on $\mathcal H$ converges in trace norm to $\operatorname{Tr}_{\mathcal K}\omega_0$, there is a sequence of pure density operators $\omega_k$ on the same tensor product such that
--
--   $$
--   \|\omega_k-\omega_0\|_1\longrightarrow0,
--   \qquad \operatorname{Tr}_{\mathcal K}\omega_k=\rho_k\quad\text{for every }k.
--   $$
--
--   This lifting statement permits simultaneous approximation of a state and its purification while preserving the specified limiting purification.
--
--   **Formalization Note** Equinumerous orthonormal coordinate sets express equality of Hilbert dimensions. The distinguished limiting purification is separate from the sequence index, which starts at zero in Lean. No fidelity assumption or finite Schmidt-rank restriction is added.
-- source:
--   Squashed entanglement in infinite dimensions, arXiv:1507.08964v5, PDF p. 4, Lemma 2

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier18.P09

open QAlgorithms.Papers.Independent.Dependency50.P33 (State PureState traceSize)

/-- Lemma 2, arXiv:1507.08964v5, PDF pp.4–5: continuous lifting to
pure states on the same tensor product, with the specified limiting
purification. Equinumerous orthonormal coordinate sets express equality of
Hilbert dimensions. No fidelity or finite-rank hypothesis is added. -/
theorem continuousPurifications {I J : Type}
    [Countable I] [Countable J] [Nonempty I] [Nonempty J]
    (hsameDimension : Nonempty (I ≃ J)) (omegaZero : PureState (I × J))
    (rho : ℕ → State I)
    (hlim : traceConverges (fun k => (rho k).coefficients)
      (partialTraceRightCoeff omegaZero.val.coefficients)) :
    ∃ omega : ℕ → PureState (I × J),
      traceConverges (fun k => (omega k).val.coefficients)
        omegaZero.val.coefficients ∧
      ∀ k, (rho k).coefficients =
        partialTraceRightCoeff (omega k).val.coefficients := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P09

end
