-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P09_su_entropy_estimate
-- name    : QAlgorithms.Papers.Independent.Extend50.P09.su_entropy_estimate
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:36:23.469988+00:00
-- url     : https://prove2.me/theorems/5ccdaa42-ac18-4978-adf0-cbcf7eff6388
-- title:
--   Appendix A2: SU(d) entropy bound
-- statement:
--   Fix an integer $d\ge2$. For $n\ge2$ let $\lambda$ partition $n-1$ with at most $d$ rows, and let $l_\lambda,r_\lambda$ be the actual Schur and Specht module dimensions. Append the physical isotypic embedding of $I_{L_\lambda}/l_\lambda\otimes|\psi_\lambda\rangle\langle\psi_\lambda|$, where $\psi_\lambda$ is a fixed unit Specht vector, to one logical $d$-level system. Conjugate by Haar measure on the determinant-one commutant of the collective $SU(d)$ action and erase one fixed known site. Errors mean optimal CPTP recovery measured in root-fidelity purified distance, with normalized Choi input and a decoder chosen before the worst reference-entangled input.
--
--   For finite positive-dimensional registers $P,Q$ and a positive operator $X^{PQ}$, write $H_{\min}(P|Q)_X=\sup\{h:\exists\sigma_Q\ge0,\ \operatorname{Tr}\sigma_Q=1,\ X\le2^{-h}I_P\otimes\sigma_Q\}$. The supremum is extended-real, so $H_{\min}(0)=+\infty$; throughout, $-\log_2 0=+\infty$.
--
--   For this entropy statement allow any $0\le t\le n$ complementary output size and any normalized reference-logical state with reference dimension at most $d$. Append the specified ancilla, before the random unitary, and form the actual Schur-decomposition $\Lambda$ with complementary partial trace retaining $t$ qudits. For fixed $\eta>0$, $n-\lambda_1\ge\eta n$ gives, uniformly over the allowed data and eventually in $n$,
--   $$H_{\min}(A^*|RE)_\Lambda\ge-2t\log_2 d+nH\!\left(\frac{\lambda_1}{n-1},\ldots,\frac{\lambda_d}{n-1}\right)-C\log_2 n.$$
--
--   Here $H$ is Shannon entropy in bits, and $C$ and the threshold depend only on $d,\eta$. This is an entropy estimate, not a multiple-erasure recovery theorem.
-- source:
--   Near-optimal covariant quantum error-correcting codes from random unitaries with symmetries, arXiv:2112.01498v2, PDF p. 16, Appendix A2: SU(d) entropy bound

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P09

noncomputable section

open scoped Matrix Matrix.Norms.Elementwise ComplexConjugate ENNReal ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Extend50.P09

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact generic definitions from the pinned accepted library.

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed bell)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalMinEntropy)

open QAlgorithms.Papers.Independent.Advance50.P02 (negLog)

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P09.covariantMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P09.covariantMatrixBorel

/-- Appendix A2, PDF p.16, (A15): entropy only, allowing arbitrary
complementary output t; this does not claim a t>1 SU(d) recovery theorem. -/
theorem su_entropy_estimate (d : ℕ) (hd : 2 ≤ d) (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, ∀ n ≥ n0, ∀ hn : 2 ≤ n,
    ∀ t : ℕ, ∀ ht : t ≤ n, ∀ lam : Schur.Partition d (n-1),
    eta*n ≤ (n : ℝ)-lam.val.rowLen 0 →
    ∀ psi : EuclideanSpace ℂ (Fin (rdim lam)), IsState psi →
    ∀ rho : Op (CovariantWord d 1 × CovariantWord d 1), IsDensityMatrix rho →
    let Psi := idTensorSuperop (R := CovariantWord d 1)
      (append (show 1 ≤ n by omega) (suAncilla lam psi)) rho
    ((-2*(t : ℝ)*Real.logb 2 d + (n : ℝ)*shapeEntropy lam - C*Real.logb 2 n : ℝ) : EReal) ≤
      conditionalMinEntropy (generalLambda ht
        (fun lam : Schur.Partition d n => ldim lam) rdim (physicalSchurBlockCoordinates d n) Psi) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P09

end
