-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_multipartite_pure_test
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.multipartite_pure_test
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:19:57.610247+00:00
-- url     : https://prove2.me/theorems/7da94487-3961-4106-a8da-56a3e5cf460e
-- title:
--   Pure multipartite separability test, (88)–(92)
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity. Here $G$ is a finite group and $U$ denotes its specified unitary representation. Raw Bose averages $\Pi=|G|^{-1}\sum_gU(g)$ use an ordinary representation; conjugation symmetry permits a projective representation.
--
--   For m≥1 nonzero finite local registers, unit pure multipartite ψ, and k≥1, the test using G=(Sk)^m and independent literal copy permutations per party accepts with Tr((⊗i ΠSym_i) ψ^⊗k).
--
--   $$
--   p_{\rm acc}=\operatorname{Tr}\!\left[\left(\bigotimes_{i=1}^m\Pi_{{\rm sym},i}^{(k)}\right)\psi^{\otimes k}\right].
--   $$
--
--   There are $m\ge1$ parties, $k\ge1$ identical copies of the pure density $\psi$, and one local symmetric projector per party.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 14, Pure multipartite separability test, (88)–(92)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P47

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P47

open scoped ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator Manifold ContDiff

open MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

variable {G S R P T A B C D R2 S2 : Type*}

variable [Fintype G] [Group G] [DecidableEq G]

variable [Fintype S] [DecidableEq S] [Nonempty S]

variable [Fintype R] [DecidableEq R] [Nonempty R]

variable [Fintype P] [DecidableEq P] [Nonempty P]

variable [Fintype T] [DecidableEq T] [Nonempty T]

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype D] [DecidableEq D] [Nonempty D]

variable [Fintype R2] [DecidableEq R2] [Nonempty R2]

variable [Fintype S2] [DecidableEq S2] [Nonempty S2]

/-- PDF p.14, (88)–(92): the multipartite pure-state acceptance formula only. -/
theorem multipartite_pure_test {m : ℕ} (hm : 0 < m) (d : Fin m → ℕ)
    (hd : ∀ i, 0 < d i) (k : ℕ) (hk : 0 < k)
    (psi : EuclideanSpace ℂ ((i : Fin m) → Fin (d i))) (hpsi : ‖psi‖ = 1) :
    controlReturnProbability (symmetryControlAverage (multiPureFamily d k)) (multiCopies (pureDensity psi) k) =
      effectProb (multiProjector d k) (multiCopies (pureDensity psi) k) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end
