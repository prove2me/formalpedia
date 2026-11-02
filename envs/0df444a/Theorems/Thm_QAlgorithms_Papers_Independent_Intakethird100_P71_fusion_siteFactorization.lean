-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P71_fusion_siteFactorization
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P71.fusion_siteFactorization
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T10:07:16.881094+00:00
-- url     : https://prove2.me/theorems/77ade1f3-a220-4073-8c86-081bc6ed1462
-- title:
--   Sitewise factorization of the fusion tensor
-- statement:
--   Let $N\ge0$, $d\ge2$, and let $A,B,C$ be arbitrary regions. Define
--
--   $$f_{A,B,C}=\left(\frac{d^3}{d^2-1}\right)^N\sum_D\delta_{B,A\cap D}\,d^{-|D|}\left(-\frac1d\right)^{|C\triangle D|}.$$
--
--   For $a_i=\mathbf1_{i\in A}$, $b_i=\mathbf1_{i\in B}$, and $c_i=\mathbf1_{i\in C}$,
--
--   $$f_{A,B,C}=\prod_i f_{a_i,b_i,c_i}.$$
--
--   The local tensor has pairs indexed by $c=0,1$: $f_{0,0,:}=(d,0)$, $f_{0,1,:}=(0,0)$, $f_{1,0,:}=(d^3,-d^2)/(d^2-1)$, and $f_{1,1,:}=(-d,d^2)/(d^2-1)$. At $N=0$ both expressions equal one. This factorizes the fusion tensor; it supplies no bound on the bond dimension of the reconstruction-coefficient solution.
-- source:
--   Classical Shadow Tomography with Locally Scrambled Quantum Dynamics, arXiv:2107.04817v4, PDF p. 22, Appendix C.3, Eqs.(C9)–(C10): sitewise fusion tensor

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P71

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ENNReal Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Intakethird100.P71

attribute [local instance] Classical.propDecidable

local notation "Config" n:max d:max =>
  QAlgorithms.Papers.Independent.Information100.P21.Config (P := Fin n) (fun _ => d)

local notation "Op" n:max d:max =>
  QAlgorithms.Papers.Independent.Information100.P21.Op (Config n d)

attribute [local instance] QAlgorithms.Papers.Independent.Intakethird100.P71.matrixContinuousENorm

local notation "Unitary" n:max d:max => Matrix.unitaryGroup (Config n d) ℂ

local notation "Local" n:max d:max => Fin n → Matrix.unitaryGroup (Fin d) ℂ

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

/-- PDF p.22 Eqs.(C9)–(C10): the regional fusion coefficient equals the
product of its site tensors. At N=0 both sides are one. This gives no
bond-dimension bound or convergence guarantee for the solution r. -/
theorem fusion_siteFactorization {n d : ℕ} (hd : 2 ≤ d) (A B C : Finset (Fin n)) :
    fusion n d A B C =
      ∏ i : Fin n, fusionSite d (decide (i ∈ A)) (decide (i ∈ B)) (decide (i ∈ C)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P71

end
