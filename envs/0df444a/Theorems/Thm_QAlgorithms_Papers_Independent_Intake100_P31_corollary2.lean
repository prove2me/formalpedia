-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P31_corollary2
-- name    : QAlgorithms.Papers.Independent.Intake100.P31.corollary2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:45:27.074376+00:00
-- url     : https://prove2.me/theorems/50158679-5e27-41ed-a971-2fcf03aedcb4
-- title:
--   Corollary 2: bound for a dual pair of surjective hash families
-- statement:
--   Let $n\ge1$, $m\le n$, and let surjective linear families $f_r:\mathbb F_2^n\to\mathbb F_2^m$ and $g_r:\mathbb F_2^n\to\mathbb F_2^{n-m}$ use the same finite nonempty uniform seed, with $\ker f_r=(\ker g_r)^\perp$ for every seed. If $\varepsilon\ge0$ and $f_r$ has collision probability at most $\varepsilon2^{-m}$ on every pair of distinct inputs, then $g_r$ has universality parameter
--
--   $$\varepsilon'=2(1-2^{-m}\varepsilon)+(\varepsilon-1)2^{n-m}.$$
--
--   Surjectivity fixes the kernel dimensions exactly.
-- source:
--   Dual universality of hash functions and its applications to quantum cryptography, arXiv:1101.0064v4, PDF p. 6, Corollary 2: bound for a dual pair of surjective hash families

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P31

open scoped BigOperators Matrix ComplexConjugate

open QAlgorithms

local instance {n : ℕ} (C : BinaryLinearCode n) : Fintype C := Fintype.ofFinite C

/-- PDF p.6, Corollary 2: exact kernel dimensions follow from surjectivity. -/
theorem corollary2 {n m : ℕ} (hn : 0 < n) (hm : m ≤ n)
    {I : Type*} [Fintype I] [Nonempty I]
    (f : I → BinaryBlock n →ₗ[ZMod 2] BinaryBlock m)
    (g : I → BinaryBlock n →ₗ[ZMod 2] BinaryBlock (n - m))
    (hf : ∀ r, Function.Surjective (f r)) (hg : ∀ r, Function.Surjective (g r))
    (hdual : ∀ r, LinearMap.ker (f r) = binDual (LinearMap.ker (g r)))
    (eps : ℝ) (heps : 0 ≤ eps) (hu : HashUniversal f eps) :
    HashUniversal g (2 * (1 - (2 : ℝ) ^ (-(m : ℝ)) * eps) +
      (eps - 1) * (2 : ℝ) ^ (n - m)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P31

end
