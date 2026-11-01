-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P43_werner_fidelity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P43.werner_fidelity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:20:51.928339+00:00
-- url     : https://prove2.me/theorems/b60963a7-6372-4cd3-9005-4459d5743562
-- title:
--   Optimal Werner-state fidelity on the NPT branch and its boundary
-- statement:
--   All operators act on a finite bipartite space $\mathbb C^d\otimes\mathbb C^d$ in a fixed product basis. Write $\Gamma=T_2$ for Bob's partial transpose and $P_m=|\psi_m\rangle\langle\psi_m|$, where $|\psi_m\rangle=m^{-1/2}\sum_i|ii\rangle$. A density operator is positive semidefinite with complex trace exactly one. An admissible PPT map is complex-linear, positive and trace preserving, and $\Gamma_{\rm out}T\Gamma_{\rm in}$ is positive on every positive operator. A PPT channel is additionally completely positive; complete positivity of the transpose-conjugated map is not required. Fidelity means the overlap $\operatorname{tr}(P_m T(\rho))$.
--
--   Let $d,m\ge2$ be independent integers and $1/2\le p\le1$. Let $F$ swap the two local factors, $P_\pm=(I\pm F)/2$, $r_\pm=d(d\pm1)/2$, and
--
--   $$\rho(p)=(1-p)\frac{P_+}{r_+}+p\frac{P_-}{r_-}.$$
--
--   Let $P_{\rm neg}$ be the negative spectral projector of $\rho(p)^\Gamma$ and set $A=(I-2P_{\rm neg}^\Gamma)/m$. Then $A$ is admissible and its isotropic PPT channel $T_A$ attains the maximal fidelity $F_m$, optimized over all admissible positive PPT maps:
--
--   $$\operatorname{tr}(\rho(p)A)=\operatorname{tr}(P_mT_A(\rho(p)))=F_m(\rho(p))=\frac{\|\rho(p)^\Gamma\|_1}m=\frac{d-2+4p}{md}.$$
--
--   Here $\|\cdot\|_1$ is the trace norm. At $p=1/2$, the negative projector is zero and $A=I/m$. This gives an attained optimum, also attained by a channel.
-- source:
--   Distillability via protocols respecting the positivity of partial transpose, arXiv:quant-ph/0104095v2, PDF p. 3, Eqs. (8)–(9) and optimality sentence

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P43

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P43

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P04
  (gamma copies bellProjector negativeProjector werner)

open QAlgorithms.Papers.Independent.Information100.P30 (IsPositiveMap)

/-- PDF p.3, (8)–(9): Werner optimality, with independent input and output dimensions.
SOURCE CORRECTION: (8) prints 0<=p<=1, but (9)'s value is valid only for p>=1/2.
We restrict to 1/2<=p<=1, as required by the preceding NPT construction; at p=1/2
P_neg=0 and A=I/m is used directly. At d=m=2,p=0 the printed value is zero,
contradicting the achievable product-state overlap 1/2. The PDF has no extra /m on
Tr[A rho(p)]. Independent moderation of this correction is required. -/
theorem werner_fidelity (d m : ℕ) (hd : 2 ≤ d) (hm : 2 ≤ m)
    (p : ℝ) (hp : 1/2 ≤ p) (hpone : p ≤ 1) :
    let rho := werner d p
    let A := negativeSpaceWitness rho m 2
    RainsFeasibleEffect m A ∧ IsPositiveConjugatePPTChannel (isotropicPreparation m A) ∧
      effectProb A rho = traceNorm (gamma rho) / (m : ℝ) ∧
      effectProb (bellProjector m) (isotropicPreparation m A rho) = traceNorm (gamma rho) / (m : ℝ) ∧
      traceNorm (gamma rho) / (m : ℝ) = ((d : ℝ) - 2 + 4*p) / ((m : ℝ)*d) ∧
      IsGreatest (positivePPTFidelityValues rho m) (traceNorm (gamma rho) / (m : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P43

end
