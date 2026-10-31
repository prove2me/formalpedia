-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P12_css_lattice_construction
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P12.css_lattice_construction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:51:38.716752+00:00
-- url     : https://prove2.me/theorems/e4167385-c612-418e-9cec-c1d06b331bb6
-- title:
--   §VI (65)–(67): CSS lattice construction
-- statement:
--   Let $N\ge1$ and let $M_q,M_p$ be nonsingular real $N\times N$ row generator matrices, with $L_p\subseteq L_q^*$ for the Euclidean integer dual. In the displayed source block order put $M=\operatorname{diag}(M_q,M_p)$. Then $M$ is nonsingular, the Gram matrix is integral, and
--
--   $$M\Omega M^T=\begin{pmatrix}0&M_qM_p^T\\-M_pM_q^T&0\end{pmatrix}.$$
--
--   All lattice vectors have integral symplectic pairings. The explicit position comb on the $p$-translation lattice is a nonzero continuous Schwartz functional fixed by the physical $p$ translations and $q$ modulations. The physical Weyl coordinates are obtained by swapping the source's grouped $(q,p)$ blocks to the grouped $(p,q)$ coefficient convention.
--
--   For the single-oscillator rectangular construction with $n\ge1$ and $\alpha>0$, the scalar generator product is $n$, so its displayed Gram matrix is $n\Omega$. This supplies an actual generalized CSS stabilizer state, rather than assuming that the common eigenspace is nonzero.
-- source:
--   Encoding a qubit in an oscillator, arXiv:quant-ph/0008040v3, PDF p. 8, §VI (65)–(67): CSS lattice construction

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P12

noncomputable section

open scoped BigOperators

open MeasureTheory Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)

namespace QAlgorithms.Papers.Independent.Intakenext100.P12

/-- Section VI (65)–(67), PDF p.8: the source's CSS row block construction. -/
theorem css_lattice_construction (N : ℕ) (hN : 0 < N)
    (Mq Mp : Matrix (Fin N) (Fin N) ℝ) (hq : Mq.det ≠ 0) (hp : Mp.det ≠ 0)
    (hdual : rowLattice Mp ⊆ euclideanDual (rowLattice Mq)) :
    let M := Matrix.fromBlocks Mq 0 0 Mp
    HasCSSDistribution N Mq Mp ∧ M.det ≠ 0 ∧ IntegralMatrix (latticeGram N M) ∧
    latticeGram N M = Matrix.fromBlocks 0 (Mq * Mp.transpose) (-(Mp * Mq.transpose)) 0 ∧
    (∀ v ∈ rowLattice M, ∀ w ∈ rowLattice M,
      ∃ k : ℤ, gkpPair N v w = k) ∧
    (∀ n : ℕ, 0 < n → ∀ alpha : ℝ, 0 < alpha →
      latticeGram 1 (Matrix.fromBlocks
        (Matrix.diagonal (fun _ : Fin 1 => Real.sqrt (2 * Real.pi) / alpha)) 0 0
        (Matrix.diagonal (fun _ : Fin 1 => n * alpha / Real.sqrt (2 * Real.pi)))) =
          (n : ℝ) • sigma 1) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P12

end
