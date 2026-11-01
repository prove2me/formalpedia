-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P98_blockSdp_strictFeasibility_attainment
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P98.blockSdp_strictFeasibility_attainment
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:54:23.31581+00:00
-- url     : https://prove2.me/theorems/0f214c0e-ef76-41e8-8445-cf25ca924d0f
-- title:
--   Strict feasibility, duality, and both optima attained
-- statement:
--   Let $X=\mathbb C^n$, $Y=\mathbb C^m$ with $n,m\ge1$, and let $\Phi:L(X)\to L(Y)$ be complex-linear with a Stinespring pair $A,B:X\to Y\otimes Z$ of minimal environment dimension $\dim Z=\operatorname{rank}J(\Phi)$. Use the concrete block triple $(\Psi,C,D)$ defined on PDF page 7, with $\Psi(P)=\operatorname{diag}(\operatorname{Tr}P_{XX},\operatorname{Tr}_Y(P_{YZ,YZ}-AP_{XX}A^*))$, $C=\operatorname{diag}(0,BB^*)$ and $D=\operatorname{diag}(1,0)$. There are operators $P_0\succ0$ and $S_0\succ0$ such that
--   $$
--   D-\Psi(P_0)\succ0,\qquad\Psi^*(S_0)-C\succ0.
--   $$
--   The primal supremum $\alpha$ and dual infimum $\beta$ are equal, finite, and both attained: there exist primal and dual feasible $P,S$ with
--   $$
--   \operatorname{Re}\operatorname{Tr}(C^*P)=\alpha=\beta=\operatorname{Re}\operatorname{Tr}(D^*S).
--   $$
--   This includes the zero map with its zero-dimensional minimal environment. The result supplies both optimality certificates for this particular SDP.
-- source:
--   Semidefinite programs for completely bounded norms, arXiv:0901.4709v2, PDF p. 8, §3, unnumbered: strict feasibility, strong duality and attainment

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P98

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakenext100.P98

/-- PDF pp.8,10--11: strict feasibility on both sides, strong duality, and
attainment of both finite optima for the concrete p.7 triple. An empty minimal
environment is allowed; no minimum eigenvalue of an empty matrix is used. -/
theorem blockSdp_strictFeasibility_attainment {n m r : ℕ} (hn : 0 < n) (hm : 0 < m)
    (Phi : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)) (A B : (Matrix (Fin m × Fin r) (Fin n) ℂ))
    (hpair : stinespringPairRepresents Phi A B) (hminimal : r = (watrousChoiMatrix Phi).rank) :
    (∃ P : (Matrix (PrimalIndex n m r) (PrimalIndex n m r) ℂ),
      P.PosDef ∧ (stinespringSdpBound r - stinespringSdpMap A P).PosDef) ∧
    (∃ S : (Matrix (DualIndex r) (DualIndex r) ℂ),
      S.PosDef ∧ (blockAdjoint A S - stinespringSdpObjective B).PosDef) ∧
    blockPrimalValue A B = blockDualValue A B ∧
    ∃ (P : (Matrix (PrimalIndex n m r) (PrimalIndex n m r) ℂ)) (S : (Matrix (DualIndex r) (DualIndex r) ℂ)),
      BlockPrimalFeasible A P ∧ BlockDualFeasible A B S ∧
      (realTracePairing (stinespringSdpObjective B) P : EReal) = blockPrimalValue A B ∧
      (realTracePairing (stinespringSdpBound r) S : EReal) = blockDualValue A B := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P98

end
