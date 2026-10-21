-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_remark5_3
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.remark5_3
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:39:30.706864+00:00
-- url     : https://prove2.me/theorems/cedba837-93d7-4bd0-9f06-3213dabc4aaa
-- title:
--   Recovery with simultaneous exact marginals
-- statement:
--   Let $\rho_{ABC}$ be a density operator on nonzero finite-dimensional complex Hilbert spaces. Write $\rho_{BC},\rho_B,\rho_C$ for its marginals and $I=I(A:C\mid B)_\rho$ in bits. There are contractions $U_B,V'_B,V''_{BC}$ commuting respectively with $\rho_B,\rho_B,\rho_{BC}$. Put $V=(V'_B\otimes1_C)V''_{BC}$ and let $P$ be the support-inverse Petz map of Eq.103 with these contractions. It is CP and trace non-increasing, retains $F(\rho,(\mathrm{id}_A\otimes P)(\rho_{AB}))\ge2^{-I/2}$, and satisfies $P(\rho_B)\le V\rho_{BC}V^\dagger\le(V'_B\otimes1_C)\rho_{BC}(V'_B\otimes1_C)^\dagger$, as well as $\operatorname{tr}_C P(\rho_B)\le\rho_B$, $\operatorname{tr}_B P(\rho_B)\le\rho_C$. Define $d_B=\rho_B-\operatorname{tr}_C P(\rho_B)$, $d_C=\rho_C-\operatorname{tr}_B P(\rho_B)$, and $t=\operatorname{tr}d_B=\operatorname{tr}d_C$. Set $\tau=d_B\otimes d_C/t^2$ when $t>0$ and $\tau=\rho_B\otimes\rho_C$ when $t=0$, and $T(X)=P(X)+(\operatorname{tr}X-\operatorname{tr}P(X))\tau$. Then $T$ is CPTP and
--
--   $$F(\rho,(\mathrm{id}_A\otimes T)(\rho_{AB}))\ge2^{-I/2},\qquad\operatorname{tr}_C T(\rho_B)=\rho_B,\quad\operatorname{tr}_B T(\rho_B)=\rho_C.$$
--
--   The completion is computed from the deficits and applies also outside the support of $\rho_B$. This yields both exact marginals with the same fidelity guarantee.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 19, Remark 5.3

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12

noncomputable section

open Filter MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P12

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP matrixPower permute)

open QAlgorithms.Papers.Independent.Information100.P80 (OperatorLE groupedPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

/-- Remark 5.3 (PDF p.19, Eq.140–141), with the original fidelity bound.
The completed channel is computed from the three commuting contractions; exact
B and C marginals are simultaneous, not an equality with the whole BC state. -/
theorem remark5_3 {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    (rho : Op (A × (B × C))) (hrho : IsDensityMatrix rho) :
    let rhoBC := traceLeft rho
    let rhoB := traceRight rhoBC
    let rhoC := traceLeft rhoBC
    ∃ (U Vprime : Op B) (Vdouble : Op (B × C)),
      Contractive U ∧ Contractive Vprime ∧ Contractive Vdouble ∧
      Commute U rhoB ∧ Commute Vprime rhoB ∧ Commute Vdouble rhoBC ∧
      let V := liftFirst Vprime * Vdouble
      let P := rotatedPetzRecovery rhoBC U V
      let T := completedPetz rhoBC U V
      TNI P ∧
      (2 : ℝ) ^ (-cmi rho / 2) ≤ rootFidelity rho (idTensorSuperop P (marginalAB rho)) ∧
      OperatorLE (P rhoB) (V * cfc Real.sqrt rhoBC * (cfc Real.sqrt rhoBC) * Vᴴ) ∧
      OperatorLE (V * rhoBC * Vᴴ) (liftFirst Vprime * rhoBC * (liftFirst Vprime)ᴴ) ∧
      OperatorLE (traceRight (P rhoB)) rhoB ∧ OperatorLE (traceLeft (P rhoB)) rhoC ∧
      IsChannel T ∧
      (2 : ℝ) ^ (-cmi rho / 2) ≤ rootFidelity rho (idTensorSuperop T (marginalAB rho)) ∧
      traceRight (T rhoB) = rhoB ∧ traceLeft (T rhoB) = rhoC := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
