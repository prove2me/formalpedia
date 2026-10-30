-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_channel_covariance_test
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.channel_covariance_test
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:23:56.500055+00:00
-- url     : https://prove2.me/theorems/8aa665b9-d2f9-48ef-8ce4-2f4bc1d5b1b4
-- title:
--   Channel covariance test, (110)–(123)
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity. Here $G$ is a finite group and $U$ denotes its specified unitary representation. Raw Bose averages $\Pi=|G|^{-1}\sum_gU(g)$ use an ordinary representation; conjugation symmetry permits a projective representation. The set $\mathrm{Sym}_G$ consists of invariant densities; $\mathrm{B\!\text{-}Sym}_G$ consists of densities supported by $\Pi$. The sets $\mathrm{SymExt}_G$ and $\mathrm{BSE}_G$ are their normalized-extension marginal analogues, tracing out precisely the stated reference register. The input includes a unit purification of $\rho_S$. The prover acts only on its purifying register, with arbitrary ancillas and a retained private environment, and returns the prescribed registers. It never acts on retained $S$. All maxima mentioned below are attained.
--
--   For a supplied unitary dilation W of a CPTP N:A→B, prepare its normalized reference-first Choi purification as in (117)–(118), then Algorithm 2 under conjugate(U_A)⊗V_B has optimum max fidelity with densities invariant under this action; value 1 iff N∘AdU(g)=AdV(g)∘N for all g.
--
--   $$
--   p^{\rm opt}=\max_{\sigma\in\mathrm{Sym}(\overline U\otimes V)}F(\Phi^{\mathcal N},\sigma),\qquad p^{\rm opt}=1\iff\mathcal N\circ\mathrm{Ad}_{U(g)}=\mathrm{Ad}_{V(g)}\circ\mathcal N\ (\forall g).
--   $$
--
--   The reference-first Choi density has entries $\Phi^{\mathcal N}_{(a,b),(a',b')}=\mathcal N(|a\rangle\langle a'|)_{b,b'}/\dim A$, and $\mathrm{Ad}_U(X)=UXU^\dagger$. The optimization is over all invariant densities.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 15, Channel covariance test, (110)–(123)

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

/-- PDF pp.15–16, (110)–(123): Algorithm 2's optimum on a normalized Choi
state, and acceptance one iff covariance of the fixed channel. The comparison
states range over every invariant density, without a Choi marginal constraint. -/
theorem channel_covariance_test [Nonempty P] [Nonempty A] [Nonempty B] (U : G → Matrix.unitaryGroup A ℂ)
    (V : G → Matrix.unitaryGroup B ℂ) (hU : IsProjectiveUnitaryLift U) (hV : IsProjectiveUnitaryLift V)
    (N : Superop A B) (hN : IsChannel N)
    (psi : EuclideanSpace ℂ (P × (A × B))) (hpsi : ‖psi‖ = 1)
    (hpur : traceLeft (pureDensity psi) = normalizedChoi N) :
    ∃ v, IsGreatest (proverValues psi
      (symTest (choiFamily (fun g => (U g : Mat A)) (fun g => (V g : Mat B))))) v ∧
    IsGreatest (symmetryFidelityValues (normalizedChoi N)
      (Sym (choiFamily (fun g => (U g : Mat A)) (fun g => (V g : Mat B))))) v ∧
    (v = 1 ↔ IsOperatorCovariant (fun g => (U g : Mat A)) (fun g => (V g : Mat B)) N) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end
