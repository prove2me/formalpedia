-- Prove2me | Theorems.Thm_PadicMeasure_ext_of_residue_disk_masses
-- name    : PadicMeasure.ext_of_residue_disk_masses
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-09-06T05:42:16.926041+00:00
-- url     : https://prove2.me/theorems/20d4e35f-40a9-48c6-b6dd-06d3a07b1dbf
-- title:
--   Bounded p-adic measures are determined by residue-disk masses
-- statement:
--   Let $p$ be prime and let $\mu,
--   u$ be continuous $\mathbf C_p$-linear functionals on $C(\mathbf Z_p^\times,\mathbf C_p)$. Suppose that for every positive depth $n$ and integer $a$ prime to $p$, there is a continuous characteristic function $g_{n,a}$ of $a+p^n\mathbf Z_p$ on the unit group on which the two functionals agree. Then
--
--   $$\mu=
--   u.$$
--
--   This is the uniqueness assertion for extending prescribed residue-disk masses to a bounded p-adic measure. The hypothesis supplies the test function pointwise and so does not depend on a particular choice of its continuous-map bundle.
-- source:
--   Supporting uniqueness and vanishing arguments for PadicMeasure.colmez_r0_moment_extension in the Mazur–Tate–Teitelbaum interpolation mission.

import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.Measure.Basic

set_option autoImplicit false
noncomputable section

theorem PadicMeasure.ext_of_residue_disk_masses {p : ℕ} [Fact p.Prime]
    (μ ν : AbstractMeasure (ℤ_[p])ˣ ℂ_[p] ℂ_[p])
    (h : ∀ n : ℕ, 0 < n → ∀ a : ℤ, IsCoprime a (p : ℤ) →
      ∃ g : C((ℤ_[p])ˣ,ℂ_[p]),
        (∀ x, g x = if PadicInt.toZModPow n x.val = (a : ZMod (p^n)) then 1 else 0) ∧
        μ g = ν g) : μ = ν := by sorry
