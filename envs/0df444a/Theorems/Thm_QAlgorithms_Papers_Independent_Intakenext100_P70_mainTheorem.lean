-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P70_mainTheorem
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P70.mainTheorem
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:40:51.675532+00:00
-- url     : https://prove2.me/theorems/30871c2c-ef5d-40aa-ae87-71fe96895da6
-- title:
--   Corrected parameterized main theorem
-- statement:
--   Let $n\geq1$ be an integer, $0<\kappa<1/2$, and
--   $$
--   (1+\kappa^n)^{-1/n}\leq p<1.
--   $$
--   There exist positive integers $N,r,m$, an integer $d\geq2$, and a weight $0<q\leq1/2$ with the following properties. Let $a,b,S,F$ be qubits, let every $A_{i,j,k}$ and $B_{i,j,k}$ have dimension $d$, and group the shield into $N$ shares with $rm$ factors per share. Define $\Gamma:aA\to bB$ from the normalized Choi state in (S18), and define the retained, measured switch channel
--   $$
--   \mathcal M=\mathcal P_0\otimes(\mathcal E_\kappa\circ\Gamma)+\mathcal P_1\otimes\mathcal E_p.
--   $$
--   Here $\mathcal E_u$ erases the entire main register with probability $u$, replacing it by its maximally mixed state and outputting a separate binary flag. The parameters satisfy (S19), $\Gamma$ is PPT-binding, and $\mathcal M$ is completely positive and trace preserving. With the all-density-input optimization and bit-valued rates defined above,
--   $$
--   Q^{(n)}(\mathcal M)=0,\qquad Q^{(N+1)}(\mathcal M)>0,\qquad Q(\mathcal M)>0.
--   $$
--   This gives the constructive family behind the undetectability result.
--
--   **Source correction.** The printed endpoint $p=1$ is excluded, as required by the intersection of parameter ranges in the source's proof.
-- source:
--   Unbounded number of channel uses are required to see quantum capacity, arXiv:1408.5115v1, PDF p. 11, Supplementary Theorem; repeated Methods Theorem, p.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P70

namespace QAlgorithms.Papers.Independent.Intakenext100.P70

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22
  (Op coherentInformation singleUseInformation quantumCapacity mixed)

/-- Methods Theorem, PDF p.3; repeated Supplementary Theorem, p.11.
SOURCE CORRECTION: the printed interval ends at p=1; here p<1, precisely the
intersection of Lemmas 3 and 4 used in its proof. At p=1 every branch is PPT-binding,
so the printed positive-capacity endpoint is false. Gamma is computed from S18. -/
theorem mainTheorem (n : ℕ) (hn : 0 < n) (kappa p : ℝ)
    (hk0 : 0 < kappa) (hk1 : kappa < 1 / 2)
    (hp0 : cubittErasureThreshold n kappa ≤ p) (hp1 : p < 1) :
    ∃ P : CubittParameters, CubittValid P ∧ CubittPPTCondition P ∧ CubittPPTBinding (cubittGammaChannel P) ∧
      IsChannel (cubittPaperChannel P kappa p) ∧
      cubittBlockInformation (cubittPaperChannel P kappa p) n = 0 ∧
      0 < cubittBlockInformation (cubittPaperChannel P kappa p) (P.N + 1) ∧
      0 < quantumCapacity (cubittPaperChannel P kappa p) := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P70
