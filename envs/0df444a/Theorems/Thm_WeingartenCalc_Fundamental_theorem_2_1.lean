-- Prove2me | Theorems.Thm_WeingartenCalc_Fundamental_theorem_2_1
-- name    : WeingartenCalc.Fundamental.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:43:04.17197+00:00
-- url     : https://prove2.me/theorems/93873f9a-fde9-4f23-b146-d9f1675c4eec
-- title:
--   Theorem 2.1 (Fundamental Theorem of Weingarten Calculus) — $I_{ij}=\sum_{x,y=1}^m A_{ix}W_{xy}A^*_{yj}$
-- statement:
--   Let $G$ be a compact Hausdorff topological group with Haar probability measure $\mu$, and let $U : G\to\mathrm{U}(N)$ be a continuous unitary representation on $H=\mathbb{C}^N$, with matrix elements $U_{xy}(g)=\langle e_x,U(g)e_y\rangle$ in the standard orthonormal basis. Fix $d\in\mathbb{N}$, and let $a_1,\dots,a_m$ be a basis of the space of $G$-invariant tensors
--   $$(H^{\otimes d})^G=\{t\in H^{\otimes d} : U^{\otimes d}(g)\,t=t\ \text{for all } g\in G\}.$$
--   Let $A=[\langle e_i,a_x\rangle]_{i\in\mathrm{Fun}(d,N),\,x\in[m]}$ be the $N^d\times m$ matrix of coordinates of the $a_x$ in the product basis $e_i=e_{i(1)}\otimes\cdots\otimes e_{i(d)}$, and let $W=(A^*A)^{-1}$ be the Weingarten matrix, the inverse of the Gram matrix of the $a_x$. Then for all multi-indices $i,j:[d]\to[N]$ the Weingarten integral
--   $$I_{ij}=\int_G \prod_{x=1}^{d} U_{i(x)j(x)}(g)\,d\mu(g)$$
--   is given by
--   $$I_{ij}=\sum_{x,y=1}^{m} A_{ix}\,W_{xy}\,A^*_{yj},\qquad A^*_{yj}=\overline{A_{jy}}.$$
--
--   This converts the computation of polynomial integrals over a compact group into invariant theory plus a matrix inversion: every Haar integral of a polynomial in the matrix elements of $U$ is a linear combination of the $I_{ij}$.
--
--   **Formalization Note** The hypotheses on $a$ are linear independence and $\operatorname{span}\{a_x\}=(H^{\otimes d})^G$. *Corrected:* the paper writes "a basis $a_1,\dots,a_m$ of $(H)^{\otimes d}$"; the same paragraph calls the $a_x$ "the basic invariants", and with a basis of all of $H^{\otimes d}$ the right side would be the identity matrix, so the basis is of $(H^{\otimes d})^G$. The statement holds for every $d\ge0$ (for $d=0$ both sides equal $1$), while the paper takes $d$ positive. $H$ is $\mathbb{C}^N$ with its standard basis, indices are 0-based, $A^*$ is the conjugate transpose, and $W$ is Mathlib's matrix inverse, a genuine inverse by linear independence.
-- source:
--   Collins, Matsumoto & Novak, The Weingarten Calculus, arXiv:2109.14890v1, p. 4, Theorem 2.1 (setting pp. 3–4, Section 2)

import Mathlib
import Definitions.Def_WeingartenCalc_Fundamental_TensorPower

open MeasureTheory Matrix

namespace WeingartenCalc.Fundamental

theorem theorem_2_1
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    [IsProbabilityMeasure μ] {N : ℕ} (U : G →* Matrix.unitaryGroup (Fin N) ℂ)
    (hU : Continuous U) (d : ℕ)
    {m : ℕ} (a : Fin m → ((Fin d → Fin N) → ℂ)) (ha : LinearIndependent ℂ a)
    (hspan : Submodule.span ℂ (Set.range a) = invariants U d)
    (i j : Fin d → Fin N) :
    ∫ g, ∏ x : Fin d, (U g : Matrix (Fin N) (Fin N) ℂ) (i x) (j x) ∂μ
      = ∑ x : Fin m, ∑ y : Fin m,
          coordMatrix a i x * weingartenMatrix a x y * (coordMatrix a)ᴴ y j := by sorry

end WeingartenCalc.Fundamental
