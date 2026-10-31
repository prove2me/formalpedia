-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P83_cyclicChargeAndTransitivity
-- name    : QAlgorithms.Papers.Independent.Intake100.P83.cyclicChargeAndTransitivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:16:40.079991+00:00
-- url     : https://prove2.me/theorems/6e1ba1cf-1ce8-4583-8468-257120fc4b4e
-- title:
--   Cyclic charges, the guarded obstruction and semi-universality
-- statement:
--   Let $p\ge2$ be an integer. On each qubit use the actual cyclic action $u(a)=\operatorname{diag}(1,e^{2\pi i a/p})$ for $a\in\mathbb Z_p$. Let $w(r)$ denote Hamming weight, and let $\mathcal V^{(p)}_{n,k}$ and $\mathcal V^{U(1)}_{n,k}$ denote exact finite products of invariant gates on at most $k$ sites for this action and for $\operatorname{diag}(1,z)$, respectively. For $n\ge1$ and $1\le k\le n$,
--
--   $$
--   \chi_r=\chi_s\ \Longleftrightarrow\ w(r)\equiv w(s)\pmod p.
--   $$
--
--   If $n<p$, then $\mathcal V^{(p)}_{n,n}=\mathcal V^{U(1)}_{n,n}$, and two-site gates are semi-universal when $n\ge2$. If $n\ge p$ and $k<p$, semi-universality fails. If $k\ge p$, equal-charge strings admit paths with steps of Hamming distance at most $k$, and
--
--   $$
--   \bigoplus_\mu SU(\mathcal H_\mu)\subseteq\mathcal V^{(p)}_{n,k}.
--   $$
--
--   The system-size guard distinguishes the genuine cyclic charge obstruction from the small-system excitation-number regime.
-- source:
--   Theory of Quantum Circuits with Abelian Symmetries, arXiv:2302.12466v3, PDF p. 8, III A / IV D: Zp charge obstruction and semi-universality

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P83

noncomputable section

open scoped BigOperators ComplexConjugate Matrix Kronecker Manifold ContDiff

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

namespace QAlgorithms.Papers.Independent.Intake100.P83

variable {A G : Type*} [Fintype A] [DecidableEq A]

/-- PDF pp.5,7-8: actual Z_p charges, the small-system U(1) coincidence, the guarded
obstruction, and transitivity/semi-universality for k >= p. -/
theorem cyclicChargeAndTransitivity (p n k : ℕ) (hp : 2 ≤ p)
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n) :
    (∀ r s : Words Bool n, sameCharge (cyclicPhases p) n r s ↔
      residueCharge p r = residueCharge p s) ∧
    (n < p → symmetricLocalGroup (cyclicPhases p) n n = symmetricLocalGroup excitationPhases n n ∧
      (2 ≤ n → SemiUniversal (cyclicPhases p) n 2)) ∧
    (p ≤ n → k < p → ¬ SemiUniversal (cyclicPhases p) n k) ∧
    (p ≤ k → TransitiveCharges (cyclicPhases p) n k ∧
      SemiUniversal (cyclicPhases p) n k) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P83

end
