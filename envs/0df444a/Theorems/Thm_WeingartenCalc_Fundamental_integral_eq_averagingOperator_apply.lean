-- Prove2me | Theorems.Thm_WeingartenCalc_Fundamental_integral_eq_averagingOperator_apply
-- name    : WeingartenCalc.Fundamental.integral_eq_averagingOperator_apply
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:42:54.047449+00:00
-- url     : https://prove2.me/theorems/6b2e4d53-34a8-4e40-b054-12b5a93018e3
-- title:
--   Section 2, p. 3 — the Weingarten integrals are the matrix elements of the Haar average: $I_{ij}=P_{ij}$
-- statement:
--   Let $G$ be a compact Hausdorff topological group with its Haar probability measure $\mu$, and let $U : G\to\mathrm{U}(N)$ be a continuous unitary representation on $H=\mathbb{C}^N$, with matrix elements $U_{xy}(g)$ in the standard basis. Fix $d\in\mathbb{N}$, and let $P=\int_G U^{\otimes d}(g)\,d\mu(g)$ be the Haar average of the tensor-power matrices $U^{\otimes d}_{ij}(g)=\prod_{x=1}^d U_{i(x)j(x)}(g)$. Then for all multi-indices $i,j : [d]\to[N]$,
--
--   $$I_{ij}=\int_G \prod_{x=1}^{d} U_{i(x)j(x)}(g)\,d\mu(g)=P_{ij}.$$
--
--   The Weingarten integrals of degree $d$ are thus the $N^{2d}$ matrix elements of a single operator on $H^{\otimes d}$; this linearizes the problem of computing them.
--
--   **Formalization Note** The left side is the scalar Haar integral of the product of matrix elements, written out; the right side is the $(i,j)$ entry of the matrix-valued Bochner integral `averagingOperator μ U d` (entrywise sup norm on matrices).
-- source:
--   Collins, Matsumoto & Novak, The Weingarten Calculus, arXiv:2109.14890v1, p. 3, Section 2 ("By continuity, we thus have that I_ij = P_ij")

import Mathlib
import Definitions.Def_WeingartenCalc_Fundamental_TensorPower

open MeasureTheory Matrix

namespace WeingartenCalc.Fundamental

theorem integral_eq_averagingOperator_apply
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    [IsProbabilityMeasure μ] {N : ℕ} (U : G →* Matrix.unitaryGroup (Fin N) ℂ)
    (hU : Continuous U) (d : ℕ)
    (i j : Fin d → Fin N) :
    ∫ g, ∏ x : Fin d, (U g : Matrix (Fin N) (Fin N) ℂ) (i x) (j x) ∂μ
      = averagingOperator μ U d i j := by sorry

end WeingartenCalc.Fundamental
