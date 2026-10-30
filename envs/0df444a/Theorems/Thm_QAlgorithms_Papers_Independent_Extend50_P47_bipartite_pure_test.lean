-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_bipartite_pure_test
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.bipartite_pure_test
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:19:24.704003+00:00
-- url     : https://prove2.me/theorems/062a2758-389c-463f-aba0-cafe5ad55568
-- title:
--   Pure bipartite separability test, (81)–(85)
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity. Here $G$ is a finite group and $U$ denotes its specified unitary representation. Raw Bose averages $\Pi=|G|^{-1}\sum_gU(g)$ use an ordinary representation; conjugation symmetry permits a projective representation.
--
--   For a unit pure ψAB and k≥1 identical copies, Algorithm 1 with identity on A copies and the literal permutation representation on B copies accepts with Tr(ΠSym ρB^⊗k). Explicitly p2=(1+t2)/2, p3=(1+3t2+2t3)/6, p4=(1+6t2+3t2²+8t3+6t4)/24 where tr=Tr(ρB^r); and p2≥p3≥p4.
--
--   $$
--   p_k=\operatorname{Tr}(\Pi_{\rm sym}^{(k)}\rho_B^{\otimes k}),\quad p_2=\frac{1+t_2}{2},\quad p_3=\frac{1+3t_2+2t_3}{6},\quad p_4=\frac{1+6t_2+3t_2^2+8t_3+6t_4}{24},\quad p_2\ge p_3\ge p_4.
--   $$
--
--   Here $\rho_B=\operatorname{Tr}_A\psi_{AB}$, $t_j=\operatorname{Tr}(\rho_B^j)$, and $\Pi_{\rm sym}^{(k)}$ averages all copy permutations on $B$.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 13, Pure bipartite separability test, (81)–(85)

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

/-- PDF pp.13–14, (81)–(85): the trace formula, all three explicit small-copy
probabilities, and their order. No all-k monotonicity claim is added. -/
theorem bipartite_pure_test [Nonempty A] [Nonempty B] (psi : EuclideanSpace ℂ (A × B)) (hpsi : ‖psi‖ = 1) :
    (∀ k : ℕ, 0 < k → bipartiteAcceptance psi k =
      effectProb (tensorSymmetrizer B k) (symmetryTensorCopies (traceLeft (pureDensity psi)) k)) ∧
    (let rho := traceLeft (pureDensity psi)
     bipartiteAcceptance psi 2 = (1 + (rho ^ 2).trace.re) / 2 ∧
     bipartiteAcceptance psi 3 = (1 + 3 * (rho ^ 2).trace.re +
       2 * (rho ^ 3).trace.re) / 6 ∧
     bipartiteAcceptance psi 4 = (1 + 6 * (rho ^ 2).trace.re +
       3 * ((rho ^ 2).trace.re) ^ 2 + 8 * (rho ^ 3).trace.re +
       6 * (rho ^ 4).trace.re) / 24) ∧
    bipartiteAcceptance psi 3 ≤ bipartiteAcceptance psi 2 ∧
    bipartiteAcceptance psi 4 ≤ bipartiteAcceptance psi 3 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end
