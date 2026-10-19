-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_assisted_message_dimension_bound
-- name    : QAlgorithms.Papers.Independent.Information100.P62.assisted_message_dimension_bound
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-19T07:36:18.191059+00:00
-- url     : https://prove2.me/theorems/9e3c66d8-050e-45d7-9cda-3870bf6754e2
-- title:
--   Finite dimension bound for entanglement-assisted zero-error messages
-- statement:
--   Let $S\subseteq L(H)$ be an operator system on a nonzero finite-dimensional complex Hilbert space. Let $A$ and $R$ be nonzero finite-dimensional ancillary spaces, let $\rho$ be a positive semidefinite operator on $A$ with trace one, and let $V_1,\ldots,V_m:A\to H\otimes R$ be isometries. Suppose that distinct messages satisfy Hilbert–Schmidt orthogonality
--
--   $$V_j\rho V_k^*\perp S\otimes L(R)\qquad(j\ne k).$$
--
--   Then
--
--   $$m\le (\dim H)^2.$$
--
--   The bound holds uniformly over both ancillary dimensions and the shared density operator. In particular, the feasible message counts in the entanglement-assisted independence number form a bounded set. This is the finite-dimension consequence of the quantum Lovász bound used to justify taking their maximum.
-- source:
--   Duan–Severini–Winter, Zero-error communication via quantum channels, non-commutative graphs and a quantum Lovász theta function, arXiv:1002.2514v2, PDF p. 10 Eq. (6) and Definition 5 (theta-tilde(S) <= |A|^2), PDF p. 11 Lemma 7 (alpha-tilde <= theta-tilde). https://arxiv.org/pdf/1002.2514v2 ; code formulation: Salzmann–Singh arXiv:2609.40054v1, PDF p. 14 Eq. (2.13).

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

noncomputable section
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P62
open scoped Matrix ComplexOrder

theorem QAlgorithms.Papers.Independent.Information100.P62.assisted_message_dimension_bound {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (S : Submodule ℂ (Matrix I I ℂ)) (hS : IsSystem S)
    {m a r : ℕ} (ha : 0 < a) (hr : 0 < r)
    (rho : Matrix (Fin a) (Fin a) ℂ) (hpos : rho.PosSemidef)
    (htr : Matrix.trace rho = 1)
    (W : Fin m → Matrix (I × Fin r) (Fin a) ℂ)
    (hW : ∀ j, (W j)ᴴ * W j = 1)
    (ho : ∀ j k, j ≠ k → ∀ X ∈ S, ∀ Y : Matrix (Fin r) (Fin r) ℂ,
      Matrix.trace ((W j * rho * (W k)ᴴ)ᴴ * Matrix.kronecker X Y) = 0) :
    m ≤ Fintype.card I ^ 2 := by sorry
