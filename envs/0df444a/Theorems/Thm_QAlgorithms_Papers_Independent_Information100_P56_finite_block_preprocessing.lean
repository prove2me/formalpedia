-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P56_finite_block_preprocessing
-- name    : QAlgorithms.Papers.Independent.Information100.P56.finite_block_preprocessing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:17:50.701001+00:00
-- url     : https://prove2.me/theorems/8a774499-647c-4527-a451-43e30bc61e16
-- title:
--   Corollary IV.2: finite-block preprocessing
-- statement:
--   Let the input alphabet be finite and nonempty, and let Bob and Eve have nonzero finite-dimensional output spaces. Each channel output is a positive semidefinite matrix of trace one. Entropies and information rates use natural logarithms, with $0\log0=0$. Let $G$ be a finite group. For $R=B,E$, let $U_R$ be a possibly projective unitary representation and $W_R(g)=U_R(g)\rho_RU_R(g)^\dagger$ for a density seed $\rho_R$. Write $\rho_R(P)=\sum_gP(g)W_R(g)$ and $\Delta(P)=H(\rho_B(P))-H(\rho_E(P))$. For $n\ge1$, let $\Delta_n$ be the entropy difference of the physical product outputs. Both $P_1$ and $P_3$ may be arbitrarily correlated laws on $G^n$. Then
--
--   $$\frac{C^{(n)}}n\ge\frac{\Delta_n(P_3*P_1)-\Delta_n(P_1)}n.$$
--
--   The maximum over the pair is attained and is denoted $R_n^{\rm pair}$. Each nonnegative rate strictly below a displayed pair value is operationally achievable with vanishing uniform-message error and full trace-norm leakage. This keeps preprocessing length distinct from subsequent coding length.
-- source:
--   From Symmetry to Secrecy: Covariant Classical--Quantum Wiretap Channels, arXiv:2610.03580v1, PDF p. 7, Corollary IV.2: finite-block preprocessing

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- Corollary IV.2, pp.7–8: arbitrary correlated distributions on the product group;
the best pair rate is attained and remains only a lower bound on full private information. -/
theorem finite_block_preprocessing
    {G B E : Type*} [Group G] [Fintype G] [Fintype B] [DecidableEq B]
    [Fintype E] [DecidableEq E] [Nonempty B] [Nonempty E]
    (UB : ProjectiveRep G B) (UE : ProjectiveRep G E)
    (rhoB : Matrix B B ℂ) (rhoE : Matrix E E ℂ)
    (hB : QAlgorithms.IsDensityMatrix rhoB) (hE : QAlgorithms.IsDensityMatrix rhoE)
    (n : ℕ) (hn : 1 ≤ n) (P1 P3 : (Fin n → G) → ℝ)
    (h1 : IsLaw P1) (h3 : IsLaw P3) :
    let WB := orbit UB rhoB
    let WE := orbit UE rhoE
    let D := delta (productOutput n WB) (productOutput n WE)
    (D (convolution P3 P1) - D P1) / n ≤ blockPrivate n WB WE / n ∧
    ∃ Q1 Q3 : (Fin n → G) → ℝ, IsLaw Q1 ∧ IsLaw Q3 ∧
      (∀ A B, IsLaw A → IsLaw B →
        (D (convolution B A) - D A) / n ≤ (D (convolution Q3 Q1) - D Q1) / n) ∧
      (D (convolution Q3 Q1) - D Q1) / n ≤ blockPrivate n WB WE / n ∧
      (∀ R : ℝ, 0 ≤ R → R < (D (convolution P3 P1) - D P1) / n →
        AchievableRate WB WE R) := by sorry

end QAlgorithms.Papers.Independent.Information100.P56

end
