-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P29_direction_scalar_sectors
-- name    : QAlgorithms.Papers.Independent.Next46.P29.direction_scalar_sectors
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:25:24.062986+00:00
-- url     : https://prove2.me/theorems/e0b9cf47-4b72-47c1-9a31-3c36691f4b9d
-- title:
--   Direction-sector scalar weights and posterior-state recovery
-- statement:
--   Use the actual highest-weight spin-$k/2$ token and spin-$1/2$ message, with $k\ge0$, normalized SU(2) Haar encoding $\mathcal E_k$, and fixed covariant recovery $\mathcal R_k$. Let $P_+$ and $P_-$ be the actual total-spin projections onto $(k+1)/2$ and $(k-1)/2$. At $k=0$, the minus sector is absent and $P_-=0$. For a qubit density operator define
--
--   $$p_+=\frac{k\rho_{00}+1}{k+1},\qquad p_-=\frac{k\rho_{11}}{k+1}.$$
--
--   Then $\operatorname{Tr}(P_\pm\mathcal E_k(\rho))=p_\pm$ and
--
--   $$\mathcal E_k(\rho)=\frac{p_+}{k+2}P_+ + \begin{cases}(p_-/k)P_-&k>0,\\0&k=0.\end{cases}$$
--
--   For every joint operator $Y$,
--
--   $$\mathcal R_k(Y)=\operatorname{Tr}(P_+Y)\left(\frac{k+1}{k+2}|0\rangle\langle0|+\frac1{k+2}|1\rangle\langle1|\right)+\operatorname{Tr}(P_-Y)|1\rangle\langle1|.$$
--
--   These sectors carry only input-dependent scalar probabilities; they have no nontrivial multiplicity space.
-- source:
--   Quantum communication using a bounded-size quantum reference frame, arXiv:0812.5040v2, PDF p. 15, §VI.B: scalar sector encoding and posterior-state recovery, Eqs.(107)–(114)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P29

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Manifold ContDiff Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Next46.P29

open QAlgorithms.Papers.Independent.Information100.P56 (IsIrreducible)

open QAlgorithms.Papers.Independent.Information100.P63 (mixed)

open QAlgorithms.Papers.Independent.Information100.P34 (dephasing)

open QAlgorithms.Papers.Independent.Information100.P71 (IsSubchannel)

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF pp.15–16, Eqs.(107)–(114): scalar encoding in the two actual total-spin
sectors and posterior-state recovery. Eq.(110)'s constant is fixed by the trace.
The minus summand is explicitly omitted at zero spin; no division by zero is used. -/
theorem direction_scalar_sectors (k : ℕ) (rho : Matrix (Fin 2) (Fin 2) ℂ)
    (hrho : IsDensityMatrix rho) :
    directionEncoding k rho =
      (((k : ℂ) * rho 0 0 + 1) / ((k + 1 : ℂ) * (k + 2))) • spinPlus k +
      (if k = 0 then 0 else
        (((k : ℂ) * rho 1 1) / ((k + 1 : ℂ) * (k : ℂ))) • spinMinus k) ∧
    (spinPlus k * directionEncoding k rho).trace =
      ((k : ℂ) * rho 0 0 + 1) / (k + 1 : ℂ) ∧
    (spinMinus k * directionEncoding k rho).trace =
      (k : ℂ) * rho 1 1 / (k + 1 : ℂ) ∧
    (∀ Y, directionRecovery k Y =
      ((spinPlus k * Y).trace) • directionPlusState k +
        ((spinMinus k * Y).trace) • Matrix.single 1 1 1) := by sorry

end QAlgorithms.Papers.Independent.Next46.P29

end
