-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P31_deterministic_coset
-- name    : QAlgorithms.Papers.Independent.Intake100.P31.deterministic_coset
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:00:11.421106+00:00
-- url     : https://prove2.me/theorems/3f61feef-06da-41de-bc11-0bd52a3011aa
-- title:
--   §V, equation (49): one extended code works for every BSC
-- statement:
--   For a normalized additive error law $P$, independent of the seed and uniformly transmitted codeword, let $\widehat P(k)=\Pr[|X|=k]$. Write $[a]_+=\max\{a,0\}$ and $F_R(k)=2^{-n[1-h(\min\{k/n,1/2\})-R]_+}$. Decoding means ML word decoding with a fixed syndrome-based deterministic tie rule, followed by quotient projection when an inner code is specified. For $s\in[0,1]$ and $p\in[0,1]$, define $E_0(s,p)=s-(1+s)\log_2(p^{1/(1+s)}+(1-p)^{1/(1+s)})$ and $E(R,p)=\max_{0\le s\le1}[-sR+E_0(s,p)]$. Given $1\le t\le n$ and an inner code $K$ with $\dim K\le t$, there exists a dimension-$t$ extension $L\ge K$, chosen independently of the BSC parameter, such that
--
--   $$\forall p\in[0,1],\qquad P_e(L/K;p)\le(n+1)2^{-nE(t/n,p)}.$$
--
--   Only the ML decoder may change with $p$.
-- source:
--   Dual universality of hash functions and its applications to quantum cryptography, arXiv:1101.0064v4, PDF p. 11, §V, equation (49): one extended code works for every BSC

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P31

open scoped BigOperators Matrix ComplexConjugate

open QAlgorithms

local instance {n : ℕ} (C : BinaryLinearCode n) : Fintype C := Fintype.ofFinite C

/-- PDF p.11 (49): one extension works for every p; dimension feasibility is explicit. -/
theorem deterministic_coset {n t : ℕ} (hn : 0 < n) (ht : 1 ≤ t) (htn : t ≤ n)
    (small : BinaryLinearCode n) (hd : Module.finrank (ZMod 2) small ≤ t) :
    ∃ large : BinaryLinearCode n, small ≤ large ∧ Module.finrank (ZMod 2) large = t ∧
      ∀ p : ℝ, p ∈ Set.Icc 0 1 → cosetWordError small large (bsc p) ≤
        (n + 1) * (2 : ℝ) ^ (-(n : ℝ) * gallagerExponent ((t : ℝ) / n) p) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P31

end
