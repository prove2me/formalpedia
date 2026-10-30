-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P07_parallelTransposition_achievable
-- name    : QAlgorithms.Papers.Independent.Extend50.P07.parallelTransposition_achievable
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:44:40.621501+00:00
-- url     : https://prove2.me/theorems/c70e01bd-4fd3-40c9-8328-81f16fa0a269
-- title:
--   Theorem 8: parallel isometry transposition is achievable
-- statement:
--   Let $1\le d\le D$ be positive integer dimensions with fixed computational bases. Write $\mathcal E_V(X)=VXV^\dagger$ for an unknown isometry $V:\mathbb C^d\to\mathbb C^D$, where $V^\dagger V=I_d$. A protocol, including its finite memory and all its operations, is fixed before $V$. Its $k$ oracle slots receive the same channel $\mathcal E_V$, and every map identity below holds on every input operator. The uniform coefficient $p\in[0,1]$ is the scale in Eq. (5); the physical outcome probability on a density matrix $\rho$ is $p\operatorname{Tr}(f(V)(\rho))$.
--
--   For every positive integer $k$, a fixed physical parallel protocol with $k$ oracle slots satisfies
--
--   $$A_{\rm succ}(\mathcal E_V^{\otimes k})(Y)=\frac{k}{Dd+k-1}V^TY(V^T)^\dagger\quad\text{for every }V,Y.$$
--
--   The transpose is in the computational basis. Its coefficient multiplies a generally trace-decreasing map, so the physical outcome probability may depend on the input state and can vanish. This is an achievable family; optimality for arbitrary $k$ is left conjectural by the source. Positive $k$ is the port construction's domain.
-- source:
--   Universal construction of decoders from encoding black boxes, arXiv:2110.00258v5, PDF p. 32, Appendix E.1 Theorem 8: parallel isometry transposition construction

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P07

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Extend50.P07

open QAlgorithms.Papers.Independent.Information100.P75 (Mat)

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P06 (Choi)

open QAlgorithms.Papers.Independent.Information100.P34 (choi fromChoi)

open QAlgorithms.Papers.Independent.Claimed50.P48 (FiniteKrausCP)

open QAlgorithms.Papers.Independent.Advance50.P05 (RectangularInstrument)

open QAlgorithms.Papers.Independent.Dependency50.P05 (ChannelChoi)

/-- arXiv:2110.00258v5 PDF pp.32--38, Theorem 8: achievability for every
positive number of ports. No all-k optimality assertion is made. -/
theorem parallelTransposition_achievable (d D k : ℕ) (hd : 0 < d)
    (hD : d ≤ D) (hk : 0 < k) :
    ∃ A : Parallel d D D d k, ∀ V : Isometry d D, ∀ X,
      A.run (oracleCopies k V) X =
        (((k : ℝ) / ((D : ℝ) * (d : ℝ) + (k : ℝ) - 1) : ℝ) : ℂ) •
          conjSuperop V.val.transpose X := by sorry

end QAlgorithms.Papers.Independent.Extend50.P07

end
