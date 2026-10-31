-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P31_kernel_correspondence
-- name    : QAlgorithms.Papers.Independent.Intake100.P31.kernel_correspondence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:42:19.344134+00:00
-- url     : https://prove2.me/theorems/37870544-89c2-47dc-b24b-adc0ec0a6760
-- title:
--   §II.A: kernel coding of linear hash families
-- statement:
--   Let $1\le m\le n$, $n\ge1$, and let $f_r:\mathbb F_2^n\to\mathbb F_2^m$ be linear maps indexed by a finite nonempty uniform seed set. For $\varepsilon\ge0$, their collision bound is equivalent to
--
--   $$\forall x\ne0,\quad\Pr_r[x\in\ker f_r]\le\varepsilon/2^m.$$
--
--   Every code of codimension at most $m$ is the kernel of such a map. For a code family and its canonical quotient maps, the collision bound with maximum output size $2^{n-t_{\min}}$ is equivalent to the dimension-$t_{\min}$ code universality bound. Kernels therefore determine universality without fixing an output basis or assuming any map has rank $m$.
-- source:
--   Dual universality of hash functions and its applications to quantum cryptography, arXiv:1101.0064v4, PDF p. 3, §II.A: kernel coding of linear hash families

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P31

open scoped BigOperators Matrix ComplexConjugate

open QAlgorithms

local instance {n : ℕ} (C : BinaryLinearCode n) : Fintype C := Fintype.ofFinite C

/-- PDF pp.3--4, (1),(4),(5): kernels determine all collision probabilities.
The codomain dimension m is declared, not inferred from a possibly smaller rank. -/
theorem kernel_correspondence {n m : ℕ} (hn : 0 < n) (hm : 1 ≤ m) (hmn : m ≤ n)
    {I : Type*} [Fintype I] [Nonempty I]
    (f : I → BinaryBlock n →ₗ[ZMod 2] BinaryBlock m) (eps : ℝ) (heps : 0 ≤ eps) :
    (HashUniversal f eps ↔ ∀ x : BinaryBlock n, x ≠ 0 →
      seedProbability (fun r => x ∈ LinearMap.ker (f r)) ≤ eps / (2 : ℝ) ^ m) ∧
    (∀ C : BinaryLinearCode n, n - Module.finrank (ZMod 2) C ≤ m →
      ∃ g : BinaryBlock n →ₗ[ZMod 2] BinaryBlock m, LinearMap.ker g = C) ∧
    (∀ C : I → BinaryLinearCode n,
      (∀ a b : BinaryBlock n, a ≠ b → seedProbability (fun r => (C r).mkQ a = (C r).mkQ b) ≤
        eps * (2 : ℝ) ^ ((minDim C : ℝ) - n)) ↔ UniversalAt C (minDim C) eps) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P31

end
