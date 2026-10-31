-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P31_type_bound
-- name    : QAlgorithms.Papers.Independent.Intake100.P31.type_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:56:04.577057+00:00
-- url     : https://prove2.me/theorems/b8e9db2f-2076-41fc-a994-bf782b25c349
-- title:
--   §V, equation (43): finite type-method error bound
-- statement:
--   For a normalized additive error law $P$, independent of the seed and uniformly transmitted codeword, let $\widehat P(k)=\Pr[|X|=k]$. Write $[a]_+=\max\{a,0\}$ and $F_R(k)=2^{-n[1-h(\min\{k/n,1/2\})-R]_+}$. Decoding means ML word decoding with a fixed syndrome-based deterministic tie rule, followed by quotient projection when an inner code is specified. Let $n\ge1$, $R\in[0,1]$, $p\in[0,1/2]$, and $\varepsilon\ge1$. For iid BSC noise, let $d(q\Vert p)$ be Bernoulli divergence in bits, infinite if $q$ assigns positive mass outside the support of $p$. Then
--
--   $$\varepsilon\sum_{k=0}^n\widehat P(k)F_R(k)\le\left\lfloor n/2+2\right\rfloor\varepsilon2^{-n\inf_{0\le q\le1/2}([1-h(q)-R]_++d(q\Vert p))}.$$
--
--   The extended-real infimum handles $p=0$ without converting forbidden off-support logarithms to zero.
-- source:
--   Dual universality of hash functions and its applications to quantum cryptography, arXiv:1101.0064v4, PDF p. 10, §V, equation (43): finite type-method error bound

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P31

open scoped BigOperators Matrix ComplexConjugate

open QAlgorithms

local instance {n : ℕ} (C : BinaryLinearCode n) : Fintype C := Fintype.ofFinite C

/-- PDF p.10 (43): floor(n/2+2), with extended bernoulliDivergenceBits at p=0. -/
theorem type_bound {n : ℕ} (hn : 0 < n) (R p eps : ℝ)
    (hR : R ∈ Set.Icc 0 1) (hp : p ∈ Set.Icc 0 (1 / 2)) (heps : 1 ≤ eps) :
    noiseBound (bsc (n := n) p) R eps ≤
      (⌊(n : ℝ) / 2 + 2⌋₊ : ℝ) * eps * expFactor n (typeExponent R p) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P31

end
