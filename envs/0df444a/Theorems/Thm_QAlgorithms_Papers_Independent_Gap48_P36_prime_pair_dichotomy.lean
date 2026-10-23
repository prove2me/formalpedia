-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P36_prime_pair_dichotomy
-- name    : QAlgorithms.Papers.Independent.Gap48.P36.prime_pair_dichotomy
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T04:59:30.311247+00:00
-- url     : https://prove2.me/theorems/91bb25eb-6b85-4fd4-a1cb-24bdcd1bddbb
-- title:
--   Theorem 13: decomposable prime-pair images have product or maximally entangled inputs
-- statement:
--   All Hilbert spaces have positive finite dimension. Channels are completely positive and trace preserving; conjugates use the same normalized pure-environment dilation. Use $X|k\rangle=|k+1\bmod d\rangle$, $Z|k\rangle=e^{2\pi ik/d}|k\rangle$, $W_{jk}=X^jZ^k$, and labels $(j,k)\in(\mathbb Z/d\mathbb Z)^2$. Let $d$ be prime and $\psi$ a unit vector on $\mathbb C^d\otimes\mathbb C^d$. Suppose exactly $D=d^2$ coefficients $c_{mn}=\operatorname{Tr}[(W_m\otimes W_n)^\dagger|\psi\rangle\langle\psi|]$ are nonzero, all of modulus one. This is the source’s $D$-decomposable pure-image condition. Then
--
--   $$
--   |\psi\rangle\langle\psi|=|u\rangle\langle u|\otimes|v\rangle\langle v|\text{ for unit }u,v,\quad\text{or}\quad\rho_1=\rho_2=I_d/d.
--   $$
--
--   Here $\rho_1,\rho_2$ are the computed marginals. The local dimension $d$ is distinguished from the total dimension $D=d^2$.
-- source:
--   Properties of Conjugate Channels with Applications to Additivity and Multiplicativity, arXiv:quant-ph/0509126v3, PDF p. 20, Theorem 13: decomposable prime-pair images have product or maximally entangled inputs

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P36

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P36

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Claimed50.P48

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy normalizedChoi)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P03 (convexRoof)

open QAlgorithms.Papers.Independent.Dependency50.P45 (holevoCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D E K L A2 B2 C2 : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype E] [DecidableEq E] [Fintype K] [DecidableEq K]

variable [Fintype L] [DecidableEq L] [Fintype A2] [DecidableEq A2]

variable [Fintype B2] [DecidableEq B2] [Fintype C2] [DecidableEq C2]

/-- Theorem 13, PDF pp.20–21: physical local dimension d; total input dimension d^2.
The hypothesis is the source's exact flat basisCoefficient support condition. -/
theorem prime_pair_dichotomy (d : ℕ) [NeZero d] (hd : Nat.Prime d)
    (psi : EuclideanSpace ℂ (Fin d × Fin d)) (hpsi : IsState psi)
    (hflat : FlatSupport (fun k : WeylLabel d × WeylLabel d => finWeyl d k.1 ⊗ₖ finWeyl d k.2)
      (pureDensity psi) (d^2)) :
    (∃ u v : EuclideanSpace ℂ (Fin d), IsState u ∧ IsState v ∧
      pureDensity psi = pureDensity u ⊗ₖ pureDensity v) ∨
    (traceRight (pureDensity psi) = (d : ℂ)⁻¹ • 1 ∧
      traceLeft (pureDensity psi) = (d : ℂ)⁻¹ • 1) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P36

end
