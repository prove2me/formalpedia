-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P01_atom_actual_sqrt_range
-- name    : QAlgorithms.Papers.Independent.Information100.P01.atom_actual_sqrt_range
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:24:35.745985+00:00
-- url     : https://prove2.me/theorems/7526d88c-696a-4443-9563-c232df0d451c
-- title:
--   Domination by a state gives an actual square-root-range preimage of norm at most one
-- statement:
--   Let $H$ be the separable complex Hilbert space of the bipartite system, and let $\rho$ be a positive trace-class operator on $H$ with trace one. Let $y\in H$ satisfy $|y\rangle\langle y|\le\rho$, equivalently $|\langle y,z\rangle|^2\le\langle z,\rho z\rangle$ for every $z\in H$. There exists $x\in(\ker\rho)^\perp$ such that
--
--   $$
--   \rho^{1/2}x=y,\qquad \|x\|\le1.
--   $$
--
--   Thus $y$ belongs to the actual range of $\rho^{1/2}$, and its inverse image on the support has norm at most one. If $y\ne0$, put $q=\|y\|^2$ and $\psi=y/\|y\|$. There is $u\in(\ker\rho)^\perp$ with $\rho^{1/2}u=\psi$ and $q\|u\|^2\le1$. This is the normalized form of the same bound and applies to every extracted atom.
--
--   **Formalization Note** The support inverse is represented by its actual preimage rather than a total inverse operator. The positive trace is expressed by its extended diagonal sum in any fixed complete countable orthonormal basis; no trace-norm topology is needed for this range assertion.
-- source:
--   On the coincidence of discrete and continuous definitions of Entanglement of Formation, arXiv:2610.18816v1, PDF p. 13, §3.6, range remark, equation (42)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P01

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P01

/-- arxiv-2610.18816v1, PDF p.13, range remark and equation (42).
Domination is written in quadratic-form notation, exactly |y><y| ≤ rho.
The support preimage states the inverse bound without totalizing an unbounded inverse.
The final clause is the source's normalized equivalent for nonzero y.
As in the source's domination argument, H denotes the whole separable bipartite
Hilbert space; its tensor factors play no role in this assertion. -/
theorem atom_actual_sqrt_range
    {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H] [Countable I]
    (b : HilbertBasis I ℂ H) (rho : H →L[ℂ] H)
    (hrho : IsTraceOneOperator b rho) (y : H)
    (hdom : ∀ z : H, ‖inner ℂ y z‖ ^ 2 ≤ (inner ℂ z (rho z)).re) :
    ∃ x : H,
      (∀ z : H, rho z = 0 → inner ℂ z x = 0) ∧
      ‖x‖ ≤ 1 ∧ CFC.sqrt rho x = y ∧
      (y ≠ 0 → ∃ u : H,
        (∀ z : H, rho z = 0 → inner ℂ z u = 0) ∧
        CFC.sqrt rho u = (‖y‖⁻¹ : ℂ) • y ∧
        ‖y‖ ^ 2 * ‖u‖ ^ 2 ≤ 1) := by sorry

end QAlgorithms.Papers.Independent.Information100.P01

end
