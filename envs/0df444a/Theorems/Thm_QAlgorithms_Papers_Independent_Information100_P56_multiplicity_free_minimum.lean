-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P56_multiplicity_free_minimum
-- name    : QAlgorithms.Papers.Independent.Information100.P56.multiplicity_free_minimum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:21:27.376394+00:00
-- url     : https://prove2.me/theorems/3834681b-945c-41bc-b433-fe2752034c30
-- title:
--   Lemma V.6: multiplicity-free invariant comparison states
-- statement:
--   Let the input alphabet be finite and nonempty, and let Bob and Eve have nonzero finite-dimensional output spaces. Each channel output is a positive semidefinite matrix of trace one. Entropies and information rates use natural logarithms, with $0\log0=0$. Let $G$ be a finite group. For $R=B,E$, let $U_R$ be a possibly projective unitary representation and $W_R(g)=U_R(g)\rho_RU_R(g)^\dagger$ for a density seed $\rho_R$. Write $\rho_R(P)=\sum_gP(g)W_R(g)$ and $\Delta(P)=H(\rho_B(P))-H(\rho_E(P))$. Set $\tau=\rho_E(P_1)$, and assume Eve's representation is an orthogonal sum of pairwise inequivalent irreducible spaces $H_j$ of dimensions $d_j>0$. For a probability law $P_J$, let $\sigma(P_J)=\bigoplus_jP_J(j)I_{d_j}/d_j$. For $1<\alpha\le2$,
--
--   $$I_\alpha(A;E)=\frac1{\alpha-1}\log\min_{P_J}\operatorname{Tr}\left[(\tau^{1/2}\sigma(P_J)^{(1-\alpha)/\alpha}\tau^{1/2})^\alpha\right].$$
--
--   The minimum is attained. Its trace objective is infinite if $\operatorname{supp}\tau\nsubseteq\operatorname{supp}\sigma(P_J)$. The order-one value is the right limit and equals the ordinary uniform-orbit Holevo information. This reduces comparison states to scalar block weights.
-- source:
--   From Symmetry to Secrecy: Covariant Classical--Quantum Wiretap Channels, arXiv:2610.03580v1, PDF p. 12, Lemma V.6: multiplicity-free invariant comparison states

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- Lemma V.6, pp.12–13: multiplicity-free invariant-state minimization, attainment,
and the one-sided order-one limit; negative powers retain the infinity support guard. -/
theorem multiplicity_free_minimum
    {G E J : Type*} [Group G] [Fintype G] [Fintype E] [DecidableEq E] [Nonempty E]
    [Fintype J] [Nonempty J]
    (UE : ProjectiveRep G E) (rhoE : Matrix E E ℂ) (hE : QAlgorithms.IsDensityMatrix rhoE)
    (P1 : G → ℝ) (h1 : IsLaw P1) (d : J → ℕ)
    (R : (j : J) → ProjectiveRep G (Fin (d j)))
    (T : (j : J) → Matrix E (Fin (d j) × Fin 1) ℂ)
    (hdec : IsIsotypic UE d (fun _ => 1) R T)
    (alpha : ℝ) (ha : 1 < alpha ∧ alpha ≤ 2) :
    let omega := induced (orbit UE rhoE) P1
    let tau := average (orbit UE rhoE) P1
    renyiInfo alpha uniform omega = renyiLog alpha (invariantMinimum d T alpha tau) ∧
    (∃ P : J → ℝ, IsLaw P ∧
      reverseSandwichedTrace alpha tau (invariantWeights d T P) = invariantMinimum d T alpha tau) ∧
    Filter.Tendsto (fun a : ℝ => (renyiInfo a uniform omega).toReal)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (holevo uniform omega)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P56

end
