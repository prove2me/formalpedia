-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P14_rotatedSqueezing
-- name    : QAlgorithms.Papers.Independent.Frontier18.P14.rotatedSqueezing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:07:40.910119+00:00
-- url     : https://prove2.me/theorems/44d895d2-6bac-41c9-a556-1247734bb3c5
-- title:
--   Opposite squeezing in balanced rotated modes
-- statement:
--   For real $\Theta$, let $S(\Theta/2)$ be the real doubled amplifier matrix (3.20), and let $R$ apply the real balanced beam matrix to annihilators and creators. Then
--
--   $$S(\Theta/2)=R^\dagger M R,$$
--
--   where $M$ mixes each rotated mode only with its own creator, with off-diagonal coefficients $+\sinh(\Theta/2)$ in mode one and $-\sinh(\Theta/2)$ in mode two. Thus $a'_1=a_1\cosh(\Theta/2)+a_1^\dagger\sinh(\Theta/2)$ and $a'_2=a_2\cosh(\Theta/2)-a_2^\dagger\sinh(\Theta/2)$ in that rotated basis. For $q=(a+a^\dagger)/\sqrt2$ and $p=i(a^\dagger-a)/\sqrt2$,
--
--   $$q'_1=e^{\Theta/2}q_1,\quad p'_1=e^{-\Theta/2}p_1,\quad q'_2=e^{-\Theta/2}q_2,\quad p'_2=e^{\Theta/2}p_2.$$
--
--   These exact core identities describe noiseless stretching of one quadrature and reciprocal squeezing of its conjugate.
-- source:
--   Quantum Physics of Simple Optical Instruments, arXiv:quant-ph/0305007v2, PDF p. 29, §6.1: two-mode amplification is opposite squeezing in rotated modes

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P14

noncomputable section

open scoped Matrix ComplexConjugate

open Filter

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier18.P14

open QAlgorithms.Papers.Independent.Dependency50.P34 (fockKet)

/-- PDF pp.29–30, (6.6)–(6.9): exact opposite single-mode squeezes
in the balanced rotated basis. Quadrature identities are on the invariant core;
there is no claim of noiseless amplification of both conjugate quadratures. -/
theorem rotatedSqueezing (theta : ℝ) :
    amplifierDoubled (theta / 2) =
      balancedDoubled.conjTranspose * oppositeSqueezes (theta / 2) * balancedDoubled ∧
    (∀ j : Fin 2,
      let s : ℂ := if j = 0 then 1 else -1
      let a := annihilate 2 j
      let ad := create 2 j
      let ap := (Real.cosh (theta / 2) : ℂ) • a + (s * (Real.sinh (theta / 2) : ℂ)) • ad
      let adp := (Real.cosh (theta / 2) : ℂ) • ad + (s * (Real.sinh (theta / 2) : ℂ)) • a
      quadratureQ ap adp =
        (Real.exp ((if j = 0 then theta else -theta) / 2) : ℂ) • quadratureQ a ad ∧
      quadratureP ap adp =
        (Real.exp ((if j = 0 then -theta else theta) / 2) : ℂ) • quadratureP a ad) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P14

end
