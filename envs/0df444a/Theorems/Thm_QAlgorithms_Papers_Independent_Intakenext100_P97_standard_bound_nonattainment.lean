-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P97_standard_bound_nonattainment
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P97.standard_bound_nonattainment
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:56:30.456407+00:00
-- url     : https://prove2.me/theorems/56565446-eb92-4734-8b79-64ef7c320dbf
-- title:
--   Pure-blank two-register unitaries do not attain the standard bound
-- statement:
--   All states are positive semidefinite, trace-one matrices, including pure and rank-deficient states. Write $F(\rho,\sigma)$ for squared Uhlmann fidelity, $f=\sqrt{F(\rho_1,\rho_2)}$, and $D(\rho,\sigma)=\sqrt{1-F(\rho,\sigma)}=\sin\Delta(\rho,\sigma)$.
--
--   Let $H=\mathbb C^d$ with $d>1$, and let $s,b\in H$ be arbitrary unit vectors. Put $\rho_1=I/d$ and $\rho_2=|s\rangle\langle s|$. For every unitary $V$ acting on $H_A\otimes H_B$ only, use the same pure blank $|b\rangle\langle b|$ for both labels and define $\widetilde\rho_j=V(\rho_j\otimes|b\rangle\langle b|)V^\dagger$. The joint-output relative error is strictly above the standard bound:
--
--   $$\frac{D(\widetilde\rho_1,\rho_1\otimes\rho_1)+D(\widetilde\rho_2,\rho_2\otimes\rho_2)}{D(\rho_1\otimes\rho_1,\rho_2\otimes\rho_2)}>f-\frac{f^2}{\sqrt{1+f^2}}.$$
--
--   This rules out saturation under P1–P2 for the specified maximally mixed/pure pairs. The claim concerns no discarded environment and imposes no conclusion on general mixed-ancilla cloners.
-- source:
--   Lower bound on the relative error of mixed-state cloning and related operations, arXiv:quant-ph/0208159v2, PDF p. 5, §V, P1–P2 and the following paragraph

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P97

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intakenext100.P97

open QAlgorithms.Papers.Independent.Information100.P67
  (squaredFidelity sineDistance receiverChannel)

open QAlgorithms.Papers.Independent.Dependency50.P48 (densityPower)

/-- PDF p.5, §V, P1--P2: a unitary on `H tensor H` with a common pure
blank cannot attain Eq. (22) for `{I/d, |s><s|}`. No environment is
silently discarded, and no assertion about general cloners is made. -/
theorem standard_bound_nonattainment {d : ℕ} (hd : 1 < d)
    (s blank : EuclideanSpace ℂ (Fin d)) (hs : IsState s) (hblank : IsState blank)
    (V : Matrix.unitaryGroup (Fin d × Fin d) ℂ) :
    let rho1 : Matrix (Fin d) (Fin d) ℂ := (1 / (d : ℂ)) • 1
    let rho2 := pureDensity s
    let out := fun rho : Matrix (Fin d) (Fin d) ℂ =>
      (V : Matrix _ _ ℂ) * Matrix.kronecker rho (pureDensity blank) * (V : Matrix _ _ ℂ)ᴴ
    standardBound (rootFidelity rho1 rho2) <
      relativeError (out rho1) (out rho2)
        (Matrix.kronecker rho1 rho1) (Matrix.kronecker rho2 rho2) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P97

end
