-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_variational_lower_bound
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.variational_lower_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:29:53.400265+00:00
-- url     : https://prove2.me/theorems/87b082c3-26fc-4bc1-957e-10899af6af10
-- title:
--   Variational acceptance gives a lower bound
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity. Here $G$ is a finite group and $U$ denotes its specified unitary representation. Raw Bose averages $\Pi=|G|^{-1}\sum_gU(g)$ use an ordinary representation; conjugation symmetry permits a projective representation. The set $\mathrm{Sym}_G$ consists of invariant densities; $\mathrm{B\!\text{-}Sym}_G$ consists of densities supported by $\Pi$. The sets $\mathrm{SymExt}_G$ and $\mathrm{BSE}_G$ are their normalized-extension marginal analogues, tracing out precisely the stated reference register. The input includes a unit purification of $\rho_S$. The prover acts only on its purifying register, with arbitrary ancillas and a retained private environment, and returns the prescribed registers. It never acts on retained $S$. All maxima mentioned below are attained.
--
--   Every valid parameterized prover channel has exact acceptance bounded by the corresponding unrestricted maximum symmetric fidelity. Hence every attained or well-defined supremum over such acceptances is bounded by that same optimum.
--
--   $$
--   p_j(\theta)\le v_j\qquad(\theta\in\Theta,\ j=2,3,4),\quad(v_2,v_3,v_4)=\left(\max_{\mathrm{Sym}}F,\max_{\mathrm{BSE}}F,\max_{\mathrm{SymExt}}F\right).
--   $$
--
--   The parameter set is $\Theta$, $p_j(\theta)$ is exact noiseless acceptance, and each $v_j$ is the attained unrestricted optimum. There is no empty-real-supremum convention and no noisy-frequency or convergence claim.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 3, Variational acceptance gives a lower bound

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

/-- PDF pp.3,19–20: every exact variational channel yields a lower bound on
its corresponding optimal symmetric fidelity; no noisy sample claim is made. -/
theorem variational_lower_bound [Nonempty S] [Nonempty R] [Nonempty P] {Theta : Type*}
    (U : G → Matrix.unitaryGroup S ℂ) (hU : IsProjectiveUnitaryLift U)
    (V : G →* Matrix.unitaryGroup (R × S) ℂ)
    (hV : symmetryControlAverage (fun g => (V g : Mat (R × S))) ≠ 0)
    (W : G → Matrix.unitaryGroup (R × S) ℂ) (hW : IsProjectiveUnitaryLift W)
    (rho : Mat S) (hrho : IsDensityMatrix rho) (psi : EuclideanSpace ℂ (P × S))
    (hpsi : ‖psi‖ = 1) (hpur : traceLeft (pureDensity psi) = rho)
    (N2 : Theta → Superop P S) (N3 : Theta → Superop P R)
    (N4 : Theta → Superop P (R × (R × S)))
    (hN2 : ∀ t, IsChannel (N2 t)) (hN3 : ∀ t, IsChannel (N3 t))
    (hN4 : ∀ t, IsChannel (N4 t)) :
    ∃ v2 v3 v4 : ℝ,
      IsGreatest (symmetryFidelityValues rho (Sym (fun g => (U g : Mat S)))) v2 ∧
      IsGreatest (symmetryFidelityValues rho (BSE (fun g => (V g : Mat (R × S))))) v3 ∧
      IsGreatest (symmetryFidelityValues rho (SE (fun g => (W g : Mat (R × S))))) v4 ∧
      ∀ t, controlReturnProbability (symTest (fun g => (U g : Mat S)))
        (firstChannel (N2 t) (pureDensity psi)) ≤ v2 ∧
        controlReturnProbability (symmetryControlAverage (fun g => (V g : Mat (R × S))))
          (firstChannel (N3 t) (pureDensity psi)) ≤ v3 ∧
        controlReturnProbability (seTest (fun g => (W g : Mat (R × S))))
          (firstChannel (N4 t) (pureDensity psi)) ≤ v4 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end
