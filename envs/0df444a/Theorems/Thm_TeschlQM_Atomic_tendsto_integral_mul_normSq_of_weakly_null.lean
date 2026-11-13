-- Prove2me | Theorems.Thm_TeschlQM_Atomic_tendsto_integral_mul_normSq_of_weakly_null
-- name    : TeschlQM.Atomic.tendsto_integral_mul_normSq_of_weakly_null
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-12T09:11:39.445908+00:00
-- url     : https://prove2.me/theorems/f07429d2-c45c-47ba-a634-5729a50adc05
-- title:
--   Rellich: $\int W|\psi_n|^2\to0$ for weakly null $H^1$-bounded $\psi_n$ and $W$ vanishing at infinity
-- statement:
--   Let $W:\mathbb R^d\to\mathbb R$ be measurable, bounded, and vanishing at infinity ($\sup_{|x|\ge R}|W|\to0$). If $\psi_n\in D(H_0)$ converge weakly to $0$ in $L^2(\mathbb R^d)$ and $\|\psi_n\|$ and $\langle\psi_n,H_0\psi_n\rangle$ are bounded, then $\int W|\psi_n|^2\,dx\to0$.
--
--   Role: the relative compactness of $W$ with respect to $H_0$ (Rellich), which kills the localization error term along a Weyl sequence.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/, Chapter 7 (relative compactness w.r.t. H_0 of multiplication by functions vanishing at infinity, Rellich); used in the proof of Theorem 11.2, p. 244

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_Shared_essentialSpectrum
import Definitions.Def_TeschlQM_Shared_IsBoundedBelowBy
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_Atomic_mulOp
import Definitions.Def_TeschlQM_Atomic_freeHamiltonian
import Definitions.Def_TeschlQM_Atomic_atomicHamiltonian
open MeasureTheory Filter

namespace TeschlQM.Atomic

theorem tendsto_integral_mul_normSq_of_weakly_null (ι : Type) [Fintype ι]
    (W : EuclideanSpace ℝ ι → ℝ) (hWm : Measurable W) (hWb : ∃ C : ℝ, ∀ x, |W x| ≤ C)
    (hWt : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x, R ≤ ‖x‖ → |W x| ≤ ε)
    (ψ : ℕ → (freeHamiltonian ι).domain)
    (hw : ∀ φ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)), Tendsto (fun n => inner ℂ φ (ψ n : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)))) atTop (nhds 0))
    (hb : ∃ B : ℝ, ∀ n, ‖(ψ n : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)))‖ ≤ B ∧
      (inner ℂ (ψ n : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) (freeHamiltonian ι (ψ n))).re ≤ B) :
    Tendsto (fun n => ∫ x, W x * ‖((ψ n : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) : EuclideanSpace ℝ ι → ℂ) x‖ ^ 2) atTop (nhds 0) := by sorry

end TeschlQM.Atomic
