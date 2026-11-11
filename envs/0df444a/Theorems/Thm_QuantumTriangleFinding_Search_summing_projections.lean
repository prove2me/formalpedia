-- Prove2me | Theorems.Thm_QuantumTriangleFinding_Search_summing_projections
-- name    : QuantumTriangleFinding.Search.summing_projections
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:25:10.302751+00:00
-- url     : https://prove2.me/theorems/ba7dcfd9-89db-48e8-a20c-6c6d42144bc5
-- title:
--   Lemma 4.4 — Summing projections
-- statement:
--   Let $(\Pi_i)_{i\in J}$ be any finite family of orthogonal projections on a finite-dimensional complex Hilbert space, and write $L=\sum_i\Pi_i$. Suppose $\gamma>0$, $\kappa\ge0$ and
--   $$L^2\succeq\gamma L,\qquad \sum_i\|[\Pi_i,L]g\|^2\le\kappa^2\langle g,Lg\rangle\quad\text{for every }g.$$
--   For every $R>0$, with $F=(I+L/R)^{-1}$, and every $f$,
--   $$\sum_i\langle\Pi_if,F\Pi_if\rangle\le\left(2+\frac{\kappa^2}{\gamma^2}\right)R\|f\|^2.$$
--   The projections need not commute. The finite family and Hilbert space may have dimension zero. Quadratic forms use their real values. This is the full abstract projection estimate, independent of a Boolean input law.
--
--   Differences from the source:
--   - encoding: a finite-dimensional complex Hilbert space and projections indexed 1,…,ℓ → EuclideanSpace ℂ K and matrices indexed by arbitrary finite types K and J; reason: orthonormal bases and finite index bijections preserve orthogonal projections, norms, quadratic forms and the actual inverse; J may be empty
-- source:
--   Arjan Cornelissen, Amin Shiraz Gilani, Xingyu Zhou, STOC 2027 submission #1375 (October 2026), Lemma 4.4, (4.21)–(4.22), p. 21

import Definitions.Def_QuantumTriangleFinding_Search_FiniteProbability

set_option autoImplicit false
open scoped BigOperators ComplexOrder
noncomputable section

namespace QuantumTriangleFinding.Search

/-- Lemma 4.4, p.21. An orthonormal basis identifies any finite complex Hilbert space with ℂ^K. -/
theorem summing_projections {J K : Type} [Fintype J] [Fintype K] [DecidableEq K]
    (P : J → Matrix K K ℂ) (hP : ∀ i, (P i).IsHermitian ∧ P i * P i = P i)
    (γ κ : ℝ) (hγ : 0 < γ) (hκ : 0 ≤ κ)
    (hgap : ((∑ i, P i) * (∑ i, P i) - (γ : ℂ) • (∑ i, P i)).PosSemidef)
    (hcomm : ∀ g : EuclideanSpace ℂ K,
      ∑ i, ‖matrixAct (commutator (P i) (∑ j, P j)) g‖ ^ 2 ≤
        κ ^ 2 * (inner ℂ g (matrixAct (∑ i, P i) g)).re)
    (R : ℝ) (hR : 0 < R) (f : EuclideanSpace ℂ K) :
    ∑ i, (inner ℂ (matrixAct (P i) f)
      (matrixAct (resolvent (∑ j, P j) R) (matrixAct (P i) f))).re ≤
        (2 + κ ^ 2 / γ ^ 2) * R * ‖f‖ ^ 2 := by sorry

end QuantumTriangleFinding.Search
