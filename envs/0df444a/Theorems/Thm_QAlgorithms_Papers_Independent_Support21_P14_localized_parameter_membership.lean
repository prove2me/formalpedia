-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P14_localized_parameter_membership
-- name    : QAlgorithms.Papers.Independent.Support21.P14.localized_parameter_membership
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:28:58.006095+00:00
-- url     : https://prove2.me/theorems/43d20e63-14c8-42f9-9750-9bb318300c80
-- title:
--   The localized parameter coefficient subring
-- statement:
--   Let $r\ge1$, and let $S$ be a commutative unital ground ring with units $\rho,q,\delta_0,u_1,\ldots,u_r$, parameters $\delta_a\in S$ for $a\ge0$, and
--   $$\rho^{-1}-\rho=(q^{-1}-q)(\delta_0-1).$$
--   Write $W_n=W_{n,S,r}(u_1,\ldots,u_r)$ for the cyclotomic BMW algebra of Definitions 2.1 and 2.8, with affine generator $y_1$ and tangle generators $e_i$.
--
--   Suppose $S$ is an integral domain and its parameters are admissible: $q-q^{-1}$ is nonzero and regular, weak admissibility holds, and $(y_1^je_1)_{0\le j<r}$ is linearly independent. In $L=S[(q-q^{-1})^{-1}]$, let
--   $$B=\mathbb Z[q,q^{-1},(q^{-1}-q)^{-1},u_1,u_1^{-1},\ldots,u_r,u_r^{-1}]\subseteq L.$$
--   Then, viewing the parameters by their canonical images in $L$,
--   $$\rho,\rho^{-1}\in B,\qquad \delta_a\in B\quad\text{for every }a\ge0.$$
--   This identifies a smaller coefficient ring for the admissible parameters. It asserts no membership of $\delta_0^{-1}$ in $B$.
-- source:
--   Cyclotomic Birman--Wenzl--Murakami algebras, II: Admissibility Relations and Freeness, arXiv:math/0612065v5, PDF p. 19, Corollary 3.8: localized coefficient subring

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P14

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Support21.P14

/-- Corollary 3.8, PDF p.19. Both rho and its inverse and every delta_a
belong to the stated localized coefficient subring. Delta_0 inverse is not
added to the conclusion or to the generating set. -/
theorem localized_parameter_membership {S : Type*} [CommRing S] [IsDomain S]
    {r : ℕ} (P : GroundParameters S r) (hadm : BMWAdmissible P) :
    algebraMap S (ParameterLocalization P) (P.rho : S) ∈ localizedCoefficientRing P ∧
    algebraMap S (ParameterLocalization P) (↑P.rho⁻¹ : S) ∈ localizedCoefficientRing P ∧
    ∀ a : ℕ, algebraMap S (ParameterLocalization P) (P.delta a) ∈ localizedCoefficientRing P := by sorry

end QAlgorithms.Papers.Independent.Support21.P14

end
