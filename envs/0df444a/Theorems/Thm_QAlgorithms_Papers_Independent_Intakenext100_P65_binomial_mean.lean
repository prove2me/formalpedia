-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P65_binomial_mean
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P65.binomial_mean
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:30:06.844823+00:00
-- url     : https://prove2.me/theorems/dcabbfb3-bd36-4640-b985-786c9e688965
-- title:
--   Binomial-code mean occupation including the single-rail corner
-- statement:
--   Let $N,S\ge0$ be integers and set $M=N+1$. Define the two full-Fock states
--
--   $$|\mu_{\rm bin}\rangle=2^{-M/2}\sum_{m=0}^M(-1)^{\mu m}\sqrt{\binom{M}{m}}\,|(S+1)m\rangle,\qquad \mu=0,1.$$
--
--   They are normalized, mutually orthogonal, and have finite first photon-number moments. For their equally weighted logical mixture,
--
--   $$\bar n_{\rm bin}=\frac12\sum_{\mu=0}^1\langle\mu_{\rm bin}|\hat n|\mu_{\rm bin}\rangle=\frac{(N+1)(S+1)}2.$$
--
--   In particular $N=S=0$ is allowed and gives mean occupation $1/2$.
-- source:
--   Performance and structure of single-mode bosonic codes, arXiv:1708.05010v3, PDF p. 11, §VI (6.2): binomial mean occupation

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P65

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P65

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Frontier18.P14 (displacementEntry)

open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)

open scoped ComplexConjugate Matrix Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.11 (6.2): all nonnegative N,S, including the single-rail corner. -/
theorem binomial_mean (N S : ℕ) :
    (∀ mu : Fin 2, fockDomain (binomialCodeCoordinates N S mu) ∧ fockNormSq (binomialCodeCoordinates N S mu) = 1 ∧
      fockMomentDomain (binomialCodeCoordinates N S mu) 1) ∧
    fockInner (binomialCodeCoordinates N S 0) (binomialCodeCoordinates N S 1) = 0 ∧
    codeMoment (binomialCodeCoordinates N S) 1 = ((N + 1 : ℕ) : ℝ) * (S + 1) / 2 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P65

end
