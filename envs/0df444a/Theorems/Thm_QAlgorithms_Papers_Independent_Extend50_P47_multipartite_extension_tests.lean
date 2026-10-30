-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_multipartite_extension_tests
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.multipartite_extension_tests
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:23:23.734904+00:00
-- url     : https://prove2.me/theorems/5e8b9e51-581c-49fc-998a-b4d8fc54a1b1
-- title:
--   Multipartite extendibility tests, (97)–(109)
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity. Here $G$ is a finite group and $U$ denotes its specified unitary representation. Raw Bose averages $\Pi=|G|^{-1}\sum_gU(g)$ use an ordinary representation; conjugation symmetry permits a projective representation. The set $\mathrm{Sym}_G$ consists of invariant densities; $\mathrm{B\!\text{-}Sym}_G$ consists of densities supported by $\Pi$. The sets $\mathrm{SymExt}_G$ and $\mathrm{BSE}_G$ are their normalized-extension marginal analogues, tracing out precisely the stated reference register. The input includes a unit purification of $\rho_S$. The prover acts only on its purifying register, with arbitrary ancillas and a retained private environment, and returns the prescribed registers. It never acts on retained $S$. All maxima mentioned below are attained.
--
--   For m≥1 and each ki≥1, form the product of permutation groups and permute ki copies of party i independently; retain each first copy. Algorithms 3 and 4 have maximum fidelities over exactly the multipartite Bose-extension and invariant-extension marginal sets (97)–(102), respectively.
--
--   $$
--   p_3^{\rm opt}=\max_{\sigma\in(k_1,\ldots,k_m)\text{-BE}}F(\rho,\sigma),\qquad p_4^{\rm opt}=\max_{\sigma\in(k_1,\ldots,k_m)\text{-E}}F(\rho,\sigma).
--   $$
--
--   The formula gives the exact characterization or operational specialization described in the cited result.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 15, Multipartite extendibility tests, (97)–(109)

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

/-- PDF p.15, (108)–(109): both multipartite extension tests, with positive
copy counts n_i+1 and precisely the first-copy marginal. -/
theorem multipartite_extension_tests [Nonempty P] {m : ℕ} (hm : 0 < m) (d n : Fin m → ℕ)
    (hd : ∀ i, 0 < d i) (rho : Mat ((i : Fin m) → Fin (d i)))
    (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (P × ((i : Fin m) → Fin (d i))))
    (hpsi : ‖psi‖ = 1) (hpur : traceLeft (pureDensity psi) = rho) :
    TestIdentity psi (symmetryControlAverage (multiFamily d n)) rho (BSE (multiFamily d n)) ∧
    TestIdentity psi (seTest (multiFamily d n)) rho (SE (multiFamily d n)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end
