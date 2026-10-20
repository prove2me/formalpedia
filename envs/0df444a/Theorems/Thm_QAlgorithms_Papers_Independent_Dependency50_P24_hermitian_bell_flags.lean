-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P24_hermitian_bell_flags
-- name    : QAlgorithms.Papers.Independent.Dependency50.P24.hermitian_bell_flags
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T16:24:42.887989+00:00
-- url     : https://prove2.me/theorems/dc97682f-ffae-4bb5-b963-3ea33e24f6a7
-- title:
--   §IV: Hermitian X and Bell flags
-- statement:
--   All spaces are finite dimensional and have positive dimension. A state means a positive semidefinite operator of trace one. The distinguished product basis $B$ is fixed and is used for both twisting and key measurement. Norms are full trace norms, fidelity $F$ is root fidelity, and logarithms are in bits.
--
--   Let $X=X^\dagger$ and $\|X\|_1=1$. Set $P=X_+$, $N=X_-$ and $p=\operatorname{Tr}P$. Then $P,N\succeq0$, $PN=0$, $X=P-N$, $0\le p\le1$, $\operatorname{Tr}N=1-p$, and
--
--   $$\gamma_X=|\psi^+\rangle\langle\psi^+|\otimes P+|\psi^-\rangle\langle\psi^-|\otimes N.$$
--
--   Here $|\psi^\pm\rangle=(|00\rangle\pm|11\rangle)/\sqrt2$. If $p>0$, $P/p$ is a state; if $p<1$, $N/(1-p)$ is a state. When both masses are positive these states are orthogonal, and the display becomes their convex mixture with weights $p,1-p$. The unnormalized formula includes $p=0,1$.
-- source:
--   General paradigm for distilling classical key from quantum states, arXiv:quant-ph/0506189v2, PDF p. 10, §IV: Hermitian X and Bell flags

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P24

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Finset

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Accepted declarations are imported rather than redeclared locally.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P04 (bellProjector)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits relativeEntanglement)

/-- PDF p.10, Eqs.(45)–(47): unnormalized spectral flags include p=0,1.
Only positive-mass branches are normalized. -/
theorem hermitian_bell_flags {S T : Type*} [Fintype S] [Fintype T]
    [Nonempty S] [Nonempty T] (X : Op (S × T)) (hherm : X.IsHermitian) (hnorm : traceNorm X = 1) :
    let P := positivePart X
    let N := negativePart X
    let p := P.trace.re
    P.PosSemidef ∧ N.PosSemidef ∧ P*N = 0 ∧ X = P-N ∧
    0 ≤ p ∧ p ≤ 1 ∧ N.trace.re = 1-p ∧
    xForm X = Matrix.kronecker (signedBell false false) P + Matrix.kronecker (signedBell false true) N ∧
    (0 < p → IsDensityMatrix ((p : ℂ)⁻¹ • P)) ∧
    (p < 1 → IsDensityMatrix (((1-p : ℝ) : ℂ)⁻¹ • N)) ∧
    (0 < p → p < 1 →
      (((p : ℂ)⁻¹ • P) * (((1-p : ℝ) : ℂ)⁻¹ • N)).trace = 0 ∧
      xForm X = (p : ℂ) • Matrix.kronecker (signedBell false false) ((p : ℂ)⁻¹ • P) +
        ((1-p : ℝ) : ℂ) • Matrix.kronecker (signedBell false true) (((1-p : ℝ) : ℂ)⁻¹ • N)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P24

end
