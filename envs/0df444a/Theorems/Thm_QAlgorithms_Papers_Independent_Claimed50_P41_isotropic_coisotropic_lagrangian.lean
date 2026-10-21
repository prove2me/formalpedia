-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P41_isotropic_coisotropic_lagrangian
-- name    : QAlgorithms.Papers.Independent.Claimed50.P41.isotropic_coisotropic_lagrangian
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:57:50.986387+00:00
-- url     : https://prove2.me/theorems/59bd23ab-3314-4db0-a455-39df0fa9c7c5
-- title:
--   §III (3.14)–(3.15): isotropic, co-isotropic, Lagrangian
-- statement:
--   Let $n\ge1$ and let $V$ be a real vector space of dimension $2n$, with a nondegenerate alternating bilinear form $B$. For a subspace $W$, put $k=\dim W$, let $r(W)$ be the rank of $B|_{W\times W}$, and put $W^\perp=\{x:B(w,x)=0\text{ for all }w\in W\}$.
--
--   $$
--   r(W)=0\iff W\text{ isotropic}\iff W\subseteq W^\perp;\qquad W\text{ co-isotropic}\iff W^\perp\subseteq W.
--   $$
--
--   Isotropic means B vanishes on W times W; co-isotropic means the complement is isotropic. Their dimensions are respectively at most and at least n. W is Lagrangian exactly when it is isotropic of dimension n, equivalently W equals its complement, and then it is both isotropic and co-isotropic.
-- source:
--   The Real Symplectic Groups in Quantum Mechanics and Optics, arXiv:quant-ph/9509002v3, PDF p. 10, §III (3.14)–(3.15): isotropic, co-isotropic, Lagrangian

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace QAlgorithms.Papers.Independent.Claimed50.P41

/-- PDF p.10, (3.14)–(3.15): all isotropic/co-isotropic equivalences,
dimension bounds and the Lagrangian case. -/
theorem isotropic_coisotropic_lagrangian (n : ℕ) (hn : 0 < n)
    (V : Type*) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (hdim : Module.finrank ℝ V = 2 * n) (B : LinearMap.BilinForm ℝ V)
    (hB : B.IsAlt) (hnd : B.Nondegenerate) (W : Submodule ℝ V) :
    (symplecticRank B W = 0 ↔ IsIsotropic B W) ∧
    (IsIsotropic B W ↔ W ≤ B.orthogonal W) ∧
    (IsIsotropic B W → Module.finrank ℝ W ≤ n) ∧
    (IsCoisotropic B W ↔ B.orthogonal W ≤ W) ∧
    (IsCoisotropic B W → n ≤ Module.finrank ℝ W) ∧
    (IsLagrangian B W ↔ IsIsotropic B W ∧ Module.finrank ℝ W = n) ∧
    (IsLagrangian B W → IsIsotropic B W ∧ IsCoisotropic B W) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P41

end
