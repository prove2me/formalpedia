-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P31_deterministic_ecc
-- name    : QAlgorithms.Papers.Independent.Intake100.P31.deterministic_ecc
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:57:45.721987+00:00
-- url     : https://prove2.me/theorems/e1386d55-e0f5-4e2d-b296-169096194582
-- title:
--   §V, equation (45): one code works for every BSC
-- statement:
--   For a normalized additive error law $P$, independent of the seed and uniformly transmitted codeword, let $\widehat P(k)=\Pr[|X|=k]$. Write $[a]_+=\max\{a,0\}$ and $F_R(k)=2^{-n[1-h(\min\{k/n,1/2\})-R]_+}$. Decoding means ML word decoding with a fixed syndrome-based deterministic tie rule, followed by quotient projection when an inner code is specified. For $s\in[0,1]$ and $p\in[0,1]$, define $E_0(s,p)=s-(1+s)\log_2(p^{1/(1+s)}+(1-p)^{1/(1+s)})$ and $E(R,p)=\max_{0\le s\le1}[-sR+E_0(s,p)]$. For every $1\le t\le n$, one can choose a dimension-$t$ binary code $C$ before choosing the BSC parameter, so that
--
--   $$\forall p\in[0,1],\qquad P_e(C;p)\le(n+1)2^{-nE(t/n,p)}.$$
--
--   The decoder may depend on $p$, while the selected code does not.
-- source:
--   Dual universality of hash functions and its applications to quantum cryptography, arXiv:1101.0064v4, PDF p. 11, §V, equation (45): one code works for every BSC

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P31

open scoped BigOperators Matrix ComplexConjugate

open QAlgorithms

local instance {n : ℕ} (C : BinaryLinearCode n) : Fintype C := Fintype.ofFinite C

/-- PDF p.11 (45): the code is chosen before the BSC parameter. -/
theorem deterministic_ecc {n t : ℕ} (hn : 0 < n) (ht : 1 ≤ t) (htn : t ≤ n) :
    ∃ C : BinaryLinearCode n, Module.finrank (ZMod 2) C = t ∧
      ∀ p : ℝ, p ∈ Set.Icc 0 1 → cosetWordError ⊥ C (bsc p) ≤
        (n + 1) * (2 : ℝ) ^ (-(n : ℝ) * gallagerExponent ((t : ℝ) / n) p) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P31

end
