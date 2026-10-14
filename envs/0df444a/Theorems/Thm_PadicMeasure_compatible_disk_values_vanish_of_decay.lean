-- Prove2me | Theorems.Thm_PadicMeasure_compatible_disk_values_vanish_of_decay
-- name    : PadicMeasure.compatible_disk_values_vanish_of_decay
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-09-06T05:42:16.754034+00:00
-- url     : https://prove2.me/theorems/b819a5f2-8721-445d-9057-6727d36c1e56
-- title:
--   Compatible disk values with uniform depth decay vanish
-- statement:
--   Let $p$ be prime and let $D(n,a)\in\mathbf C_p$ be values on positive-depth unit residue disks. Suppose
--
--   $$D(n,a)=\sum_{b=0}^{p-1}D(n+1,a+bp^n).$$
--
--   Assume there is a real sequence $B(n)\to0$ such that $|D(n,a)|_p\le B(n)$ for every positive $n$ and every integer $a$ prime to $p$. Then $D(n,a)=0$ for all these disks.
--
--   This is the vanishing mechanism used to identify prescribed higher moments with those of the measure constructed from degree-zero masses in the Colmez order-zero extension theorem.
-- source:
--   Supporting uniqueness and vanishing arguments for PadicMeasure.colmez_r0_moment_extension in the Mazur–Tate–Teitelbaum interpolation mission.

import Mathlib.NumberTheory.Padics.Complex
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Filter

theorem PadicMeasure.compatible_disk_values_vanish_of_decay {p : ℕ} [Fact p.Prime] (D : ℕ → ℤ → ℂ_[p])
    (hadd : ∀ n : ℕ, 0 < n → ∀ a : ℤ, IsCoprime a (p : ℤ) →
      (∑ b ∈ Finset.range p, D (n+1) (a+(b : ℤ)*(p : ℤ)^n)) = D n a)
    (B : ℕ → ℝ) (hB : Filter.Tendsto B Filter.atTop (nhds 0))
    (hbound : ∀ n : ℕ, 0 < n → ∀ a : ℤ, IsCoprime a (p : ℤ) → ‖D n a‖ ≤ B n) :
    ∀ n : ℕ, 0 < n → ∀ a : ℤ, IsCoprime a (p : ℤ) → D n a = 0 := by sorry
