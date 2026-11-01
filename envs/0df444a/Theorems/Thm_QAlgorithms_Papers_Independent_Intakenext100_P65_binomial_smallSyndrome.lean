-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P65_binomial_smallSyndrome
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P65.binomial_smallSyndrome
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:32:51.620747+00:00
-- url     : https://prove2.me/theorems/6961cc1d-55f2-4482-9db1-bade3893cd95
-- title:
--   bin(2,1) syndrome unitary and its eigenspaces
-- statement:
--   For bin$(N=2,S=1)$, let $c_0,c_1$ be the normalized codewords, supported on occupations $0,2,4,6$. In the invariant space $\operatorname{span}\{|0\rangle,\ldots,|6\rangle\}$ define $r_\mu=(\hat n-3)c_\mu/\sqrt3$, $a_\mu=\hat a c_\mu/\sqrt3$, and $u=(|1\rangle-|5\rangle)/\sqrt2$. These seven vectors form an orthonormal basis. Embed the standard spin-$3/2$ $J_x$ on the even occupations and spin-$1$ $J_x$ on the odd occupations. Then the unitary
--
--   $$U=\exp\!\left(\frac{2\pi i}{5}\left[8J_{x,\rm even}^2+J_{x,\rm odd}^2\right]\right)$$
--
--   has eigenvalues $e^{6\pi i/5}$ on $c_0,c_1$, $e^{4\pi i/5}$ on $r_0,r_1$, $e^{2\pi i/5}$ on $a_0,a_1$, and $1$ on $u$. Thus its eigenspaces distinguish the listed error sectors without distinguishing the logical label. The dephasing residual coefficient is $\sqrt3$; printed (6.20)'s coefficient 2 is false. Identity extension acts outside this finite invariant subspace.
-- source:
--   Performance and structure of single-mode bosonic codes, arXiv:1708.05010v3, PDF p. 17, §VI D (6.21), Tables II–III: bin(2,1) syndrome unitary

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P65

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P65

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Frontier18.P14 (displacementEntry)

open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)

open scoped ComplexConjugate Matrix Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.17 (6.21), Table III: orthonormal syndrome eigenspaces for I,a,n.
The seven-dimensional space is an invariant subspace of this finite-support example,
not a global oscillator cutoff. Printed (6.20) uses coefficient 2; the residual
is normalized by sqrt(3), its actual norm from variance 3, to preserve the
Table III rays. The printed equality itself remains separately deferred. -/
theorem binomial_smallSyndrome :
    (let B : Matrix (Fin 7) (Fin 7) ℂ := fun n j => smallBasis j n
     Bᴴ * B = 1) ∧
    smallUnitaryᴴ * smallUnitary = 1 ∧
    (∀ j : Fin 7, smallUnitary.mulVec (smallBasis j) =
      Complex.exp (Complex.I * (if j.val < 2 then 6 * Real.pi / 5
        else if j.val < 4 then 4 * Real.pi / 5 else if j.val < 6 then 2 * Real.pi / 5 else 0)) •
          smallBasis j) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P65

end
