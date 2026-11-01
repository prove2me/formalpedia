-- Prove2me | Theorems.Thm_StochKolmogorov_Persist_kolmogorov_face_box_tv_overlap
-- name    : StochKolmogorov.Persist.kolmogorov_face_box_tv_overlap
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-31T18:10:59.152418+00:00
-- url     : https://prove2.me/theorems/44879068-5cf9-4498-8e50-0977341af71f
-- title:
--   Total-variation overlap of the transition probabilities on compact boxes of an open face
-- statement:
--   Let $X$ be the solution family of the stochastic Kolmogorov system $dX_i = X_i f_i(X)\,dt + X_i g_i(X)\,dE_i(t)$, with $f_i, g_i$ locally Lipschitz on $\mathbb R^n_+$ and the nondegeneracy condition (part (1) of Assumption 1.1): the matrix $(g_i(x)g_j(x)\sigma_{ij})_{ij}$ is positive definite for every $x\in\mathbb R^n_+$. Let $I\subseteq\{1,\dots,n\}$ and $0<\alpha\le\beta$, and let $K=\{x\in\mathbb R^{I,\circ}_+ : \alpha\le x_i\le\beta\ (i\in I)\}$ be a compact box of the open face $\mathbb R^{I,\circ}_+=\{x: x_i=0\ (i\notin I),\ x_i>0\ (i\in I)\}$. Then there are $T\ge0$ and $\varepsilon>0$ such that
--
--   $$\|P(T,x,\cdot)-P(T,y,\cdot)\|_{TV}\le 1-\varepsilon\qquad\text{for all } x,y\in K,$$
--
--   where $\|\mu-\nu\|_{TV}=\sup_A|\mu(A)-\nu(A)|$.
--
--   Role: this is the minorization $P(T,x,\cdot)\ge m_{K,D}$ ($x\in K$, $m_{K,D}$ a nontrivial measure) of the proof of Lemma 3.6, applied to the process on the open face $\mathbb R^{I,\circ}_+$ (where it is again a nondegenerate Kolmogorov system in the coordinates $i\in I$). It gives at most one invariant probability measure on each open face, hence finitely many ergodic invariant measures on the boundary, as used for the minimum in (4.1).
-- source:
--   A. Hening, D. H. Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, https://arxiv.org/abs/1704.06984, Lemma 3.6 (p. 14) and its proof in the Appendix (p. 32: P(t,x,B) >= m_{K,D}(B) for x in K), applied on the open faces R^{I,o}_+; used for (4.1), p. 16

import Mathlib
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Persist_Persistence
import Definitions.Def_TotalVariationDist
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Persist

open EthierKurtz

theorem kolmogorov_face_box_tv_overlap {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    (hpd : ∀ x ∈ orthant n, (Matrix.of fun i j => C.g i x * C.g j x * C.sig i j).PosDef)
    (I : Finset (Fin n)) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) :
    ∃ T : ℝ≥0, ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ faceOpen I, (∀ i ∈ I, α ≤ x i ∧ x i ≤ β) →
      ∀ y ∈ faceOpen I, (∀ i ∈ I, α ≤ y i ∧ y i ≤ β) →
        MarkovChainCLT.tvDist (trans P X T x) (trans P X T y) ≤ 1 - ε := by sorry

end StochKolmogorov.Persist
