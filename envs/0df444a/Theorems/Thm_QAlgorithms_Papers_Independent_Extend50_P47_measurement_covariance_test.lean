-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_measurement_covariance_test
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.measurement_covariance_test
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:24:42.786119+00:00
-- url     : https://prove2.me/theorems/cf8aa93b-39c6-4680-84cd-5257fd41728d
-- title:
--   POVM covariance test, (124)–(140)
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity. Here $G$ is a finite group and $U$ denotes its specified unitary representation. Raw Bose averages $\Pi=|G|^{-1}\sum_gU(g)$ use an ordinary representation; conjugation symmetry permits a projective representation. The set $\mathrm{Sym}_G$ consists of invariant densities; $\mathrm{B\!\text{-}Sym}_G$ consists of densities supported by $\Pi$. The sets $\mathrm{SymExt}_G$ and $\mathrm{BSE}_G$ are their normalized-extension marginal analogues, tracing out precisely the stated reference register. The input includes a unit purification of $\rho_S$. The prover acts only on its purifying register, with arbitrary ancillas and a retained private environment, and returns the prescribed registers. It never acts on retained $S$. All maxima mentioned below are attained.
--
--   For a finite POVM Λ on S, specified projective U(g) and a specified permutation action πg on outcome labels X, define M(ρ)=Σx Tr(Λxρ)|x⟩⟨x|. With a supplied coherent measurement dilation, the normalized Choi test has optimum invariant-state fidelity and accepts optimally with probability 1 iff U(g)†ΛxU(g)=Λπg^{-1}(x) for all g,x.
--
--   $$
--   \Phi^{\mathcal M}=\frac1{\dim S}\sum_x\Lambda_x^T\otimes|x\rangle\langle x|,\quad p^{\rm opt}=\max_{\sigma\in\mathrm{Sym}(\overline U\otimes W)}F(\Phi^{\mathcal M},\sigma),\quad p^{\rm opt}=1\iff U(g)^\dagger\Lambda_xU(g)=\Lambda_{\pi_g^{-1}(x)}\ (\forall g,x).
--   $$
--
--   The POVM effects $\Lambda_x\succeq0$ sum to $I_S$. The supplied label action $\pi_g$ has permutation matrix $W(g)$. The normalized Choi state uses $\dim S$, correcting the printed $|X|$ in (131),(133).
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 16, POVM covariance test, (124)–(140)

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

/-- PDF pp.16–17, (124)–(140). Source correction: (131),(133) print |X|;
the constructed normalized Choi state uses dim S, as (116),(134) require.
The test is relative to the supplied indexed action, (130). -/
theorem measurement_covariance_test [Nonempty S] [Nonempty P] {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (U : G → Matrix.unitaryGroup S ℂ) (hU : IsProjectiveUnitaryLift U)
    (pi : G →* Equiv.Perm X) (L : X → Mat S) (hL : IsPOVM L)
    (psi : EuclideanSpace ℂ (P × (S × X))) (hpsi : ‖psi‖ = 1)
    (hpur : traceLeft (pureDensity psi) = normalizedChoi (povmOutcomeChannel L)) :
    ∃ v, IsGreatest (proverValues psi (symTest
      (choiFamily (fun g => (U g : Mat S)) (fun g => outcomeMatrix (pi g))))) v ∧
    IsGreatest (symmetryFidelityValues (normalizedChoi (povmOutcomeChannel L))
      (Sym (choiFamily (fun g => (U g : Mat S)) (fun g => outcomeMatrix (pi g))))) v ∧
    (v = 1 ↔ ∀ g x, (U g : Mat S)ᴴ * L x * (U g : Mat S) = L ((pi g).symm x)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end
