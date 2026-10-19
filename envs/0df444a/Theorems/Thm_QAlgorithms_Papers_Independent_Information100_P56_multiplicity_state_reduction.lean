-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P56_multiplicity_state_reduction
-- name    : QAlgorithms.Papers.Independent.Information100.P56.multiplicity_state_reduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:22:11.18842+00:00
-- url     : https://prove2.me/theorems/b1e8f34c-47e1-438f-926a-7b710d634a00
-- title:
--   Remark V.7: invariant-state reduction with multiplicities
-- statement:
--   Let the input alphabet be finite and nonempty, and let Bob and Eve have nonzero finite-dimensional output spaces. Each channel output is a positive semidefinite matrix of trace one. Entropies and information rates use natural logarithms, with $0\log0=0$. Let $G$ be a finite group. For $R=B,E$, let $U_R$ be a possibly projective unitary representation and $W_R(g)=U_R(g)\rho_RU_R(g)^\dagger$ for a density seed $\rho_R$. Write $\rho_R(P)=\sum_gP(g)W_R(g)$ and $\Delta(P)=H(\rho_B(P))-H(\rho_E(P))$. Allow finite multiplicity spaces in Eve's orthogonal isotypic decomposition. The group twirl of every density state has the form
--
--   $$\bigoplus_j\frac{I_{d_j}}{d_j}\otimes A_j,\qquad A_j\succeq0,\quad\sum_j\operatorname{Tr}A_j=1.$$
--
--   For $1<\alpha\le2$, the invariant-state comparison minimum for the uniform orbit is attained over exactly these block states, using the same support-aware trace objective as Lemma V.6. This retains the full multiplicity matrices instead of scalar weights.
-- source:
--   From Symmetry to Secrecy: Covariant Classical--Quantum Wiretap Channels, arXiv:2610.03580v1, PDF p. 13, Remark V.7: invariant-state reduction with multiplicities

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- Remark V.7, p.13: twirl block form with arbitrary multiplicity spaces and
comparison-state reduction over precisely those blocks, with an attained minimum. -/
theorem multiplicity_state_reduction
    {G E J : Type*} [Group G] [Fintype G] [Fintype E] [DecidableEq E] [Nonempty E]
    [Fintype J] [Nonempty J]
    (UE : ProjectiveRep G E) (rhoE : Matrix E E ℂ) (hE : QAlgorithms.IsDensityMatrix rhoE)
    (P1 : G → ℝ) (h1 : IsLaw P1) (d m : J → ℕ)
    (R : (j : J) → ProjectiveRep G (Fin (d j)))
    (T : (j : J) → Matrix E (Fin (d j) × Fin (m j)) ℂ)
    (hdec : IsIsotypic UE d m R T)
    (alpha : ℝ) (ha : 1 < alpha ∧ alpha ≤ 2) :
    let valid := fun A : (j : J) → Matrix (Fin (m j)) (Fin (m j)) ℂ =>
      (∀ j, (A j).PosSemidef) ∧ ∑ j, (A j).trace.re = 1
    (∀ sigma : Matrix E E ℂ, QAlgorithms.IsDensityMatrix sigma →
      ∃ A, valid A ∧ average (fun g => orbit UE sigma g) uniform = invariantBlocks d m T A) ∧
    (∃ A, valid A ∧
      renyiInfo alpha uniform (induced (orbit UE rhoE) P1) =
        renyiLog alpha (reverseSandwichedTrace alpha (average (orbit UE rhoE) P1)
          (invariantBlocks d m T A)) ∧
      ∀ Aother, valid Aother →
        reverseSandwichedTrace alpha (average (orbit UE rhoE) P1) (invariantBlocks d m T A) ≤
          reverseSandwichedTrace alpha (average (orbit UE rhoE) P1)
            (invariantBlocks d m T Aother)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P56

end
