-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P34_explicit_dio_testers
-- name    : QAlgorithms.Papers.Independent.Information100.P34.explicit_dio_testers
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:25:38.202063+00:00
-- url     : https://prove2.me/theorems/5689e564-721c-4df3-a1ac-0be8a0db4037
-- title:
--   Lemma 18: four explicit DIO channels used as compatibility testers
-- statement:
--   Let systems $1,2,B$ have finite positive dimensions, with $B=B_{2j}\otimes\widetilde B$ and $d_{B_{2j}}\ge2$. Fix computational multi-indices $\vec k,\vec l$ of $\widetilde B$ and set $|\psi^\pm\rangle=(|0,\vec k\rangle\pm|1,\vec l\rangle)/\sqrt2$. Write $P_\pm=|\psi^\pm\rangle\langle\psi^\pm|$, $H=P_++P_-$, $Z=P_+-P_-$ and $A=|\psi^+\rangle\langle\psi^-|-|\psi^-\rangle\langle\psi^+|$. Fix indices $k,l$ on system $1$ and $n,m$ on system $2$. Define
--
--   $$D=(I_1-|k\rangle\langle k|-|l\rangle\langle l|)\otimes I_2/d_2\otimes I_B/d_B,$$
--   $$Q=\left[I_{1B}-\tfrac12(|k\rangle\langle k|+|l\rangle\langle l|)\otimes H\right]\otimes I_2/d_2.$$
--
--   The factors of $Q$ are permuted into order $1,2,B$. Put $E_{xy}=|x\rangle\langle y|$ for basis labels $x,y$ of system $1,2$, and set
--
--   $$T_+=\tfrac12(E_{kn,kn}+E_{lm,lm})\otimes H+\tfrac12(E_{kn,lm}+E_{lm,kn})\otimes Z,$$
--   $$T_-=\tfrac12(E_{kn,kn}+E_{lm,lm})\otimes H+\tfrac12(E_{kn,lm}-E_{lm,kn})\otimes A.$$
--
--   Define $J_N=D+T_+$, $J_M=D+T_-$, $J_K=Q+T_+$ and $J_L=Q+T_-$. Then
--
--   $$k\ne l\ \Longrightarrow\ J_N,J_M\text{ are Choi matrices of DIO channels }1\to2B\text{, hence MIO channels},$$
--   $$n\ne m\ \Longrightarrow\ J_K,J_L\text{ are Choi matrices of DIO channels }1B\to2\text{, hence DI channels}.$$
--
--   All Choi matrices are unnormalized and input-first after the indicated regrouping. Each channel is reconstructed explicitly from its matrix. The first implication permits $n=m$ and the second permits $k=l$. The residual register may be trivial. These channel families supply compatibility testers.
-- source:
--   The Structure of Higher-Order Quantum Resources with an Application to Coherence, arXiv:2609.40186v1, PDF p. 25, Lemma 18

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P34

/-- Lemma 18, Eqs.(C1-C7), PDF pp.25-27. The four matrices are computed,
not postulated channels. The first pair requires k != l only; the second n != m only. -/
theorem explicit_dio_testers {a b c : ℕ} {R : Type*}
    [Fintype R] [DecidableEq R] [Nonempty R]
    (ha : 0 < a) (hb : 0 < b) (hc : 2 ≤ c)
    (k l : Fin a) (n m : Fin b) (kr lr : R) :
    let plus := testerPsi hc kr lr false
    let minus := testerPsi hc kr lr true
    let JN := testerAsCreation (testerD k l + testerTerm k l n m plus minus false)
    let JM := testerAsCreation (testerD k l + testerTerm k l n m plus minus true)
    let JK := testerAsDetection (testerQ k l plus minus + testerTerm k l n m plus minus false)
    let JL := testerAsDetection (testerQ k l plus minus + testerTerm k l n m plus minus true)
    (k ≠ l → FreeChoi .dio JN ∧ FreeChoi .mio JN ∧
      FreeChoi .dio JM ∧ FreeChoi .mio JM) ∧
    (n ≠ m → FreeChoi .dio JK ∧ FreeChoi .di JK ∧
      FreeChoi .dio JL ∧ FreeChoi .di JL) := by sorry

end QAlgorithms.Papers.Independent.Information100.P34

end
