-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P37_unitaryConstruction_ppt_positiveKey
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P37.unitaryConstruction_ppt_positiveKey
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:21:18.58919+00:00
-- url     : https://prove2.me/theorems/be00a50e-7bc7-4773-990c-e41f7d8b6f72
-- title:
--   Unnumbered construction, Eqs.9–12: PPT-invariant key-bearing states rho_U
-- statement:
--   Let $d\ge1$ and let $U=(u_{ij})$ be any unitary on $\mathbb C^d$. Define $W_U=\sum_{ij}u_{ij}|ij\rangle\langle ji|$, let $\Gamma$ transpose $B'$ only, and put $s=\sum_{ij}|u_{ij}|$, $p_1=s/(s+d)$, and $p_2=d/(s+d)$. Construct $\rho_U$ by Eq. (9) with $X_1=W_U/s$ and $X_2=W_U^\Gamma/d$, retaining its two distinct positive square roots. Then $\rho_U$ is a density matrix, invariant under transposition of the physical Bob registers $BB'$, and
--
--   $$\|W_U\|_1=s,\quad\|W_U^\Gamma\|_1=d,\quad p_1,p_2>0,\quad p_1+p_2=1,\quad\frac{p_1}{p_2}=\frac{s}{d}.$$
--
--   If $U$ has more than $d$ nonzero entries, then $r_U=1-h(p_1)>0$, $K_D(\rho_U)\ge r_U$, and measuring $A,B$ followed by one sequence of forward public-discussion protocols achieves $r_U$ for every purifying Eve. In this case $\rho_U$ is nonseparable across $AA':BB'$ and its LOCC Bell-pair yield is zero. This constructs the state from $U$ rather than assuming witnesses for the blocks or the weights. Equivalently, when implementing this Eq. (9) matrix through the Alice-key flip of Eq. (1), the second unflipped private bit is the X-form of $X_2^\dagger$, because that flip reverses the two odd corner blocks.
-- source:
--   Low dimensional bound entanglement with one-way distillable cryptographic key, arXiv:quant-ph/0506203v1, PDF p. 2, Unnumbered construction, Eqs.9–12: PPT-invariant key-bearing states rho_U

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P37

noncomputable section

open scoped Matrix BigOperators ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P37

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Dependency50.P24
  (Key IsPrivate xForm twist twistingMatrix associatedCCQ transposeSecond transposeBob partyCut)

/-- PDF p.2, Eqs.(9)--(12): construction from U itself, PPT invariance on BB',
and strictly positive one-way key whenever there are more than d nonzero entries.
Printed root slips after Eq.(11) are corrected: the roots of WW-adjoint and
W-adjoint-W have diagonals |u_ij| and |u_ji|, respectively; observation (ii)
concerns the shield partial transpose of W. These actual roots are computed
by xForm, since direct multiplication determines them uniquely. The odd upper
block is X2 as in Eq.(9), using xForm (X2 adjoint) before the Alice-key flip. -/
theorem unitaryConstruction_ppt_positiveKey {d : ℕ} (hd : 0 < d)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
    let V : Op (Fin d) := U
    IsDensityMatrix (rhoUnitary V) ∧ transposeBob (rhoUnitary V) = rhoUnitary V ∧
    traceNorm (weightedSwap V) = entrySum V ∧
    traceNorm (transposeSecond (weightedSwap V)) = d ∧
    0 < weightOne V ∧ 0 < weightTwo V ∧ weightOne V + weightTwo V = 1 ∧
    weightOne V / weightTwo V = entrySum V / d ∧
    (d < nonzeroEntries V →
      0 < 1-binEntropy2 (weightOne V) ∧
      HasMeasuredOneWayRate (rhoUnitary V) (1-binEntropy2 (weightOne V)) ∧
      ENNReal.ofReal (1-binEntropy2 (weightOne V)) ≤
        Gap48.P42.distillableKey (physicalFin (rhoUnitary V)) ∧
      ¬ Entanglement.IsSeparableDensity (partyCut (rhoUnitary V)) ∧
      Gap48.P42.bipartiteDistillable (physicalFin (rhoUnitary V)) = 0) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P37

end
