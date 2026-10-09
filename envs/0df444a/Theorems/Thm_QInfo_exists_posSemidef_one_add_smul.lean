-- Prove2me | Theorems.Thm_QInfo_exists_posSemidef_one_add_smul
-- name    : QInfo.exists_posSemidef_one_add_smul
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-08T23:31:00.573983+00:00
-- url     : https://prove2.me/theorems/009422eb-225b-4dab-b351-b2e81d428ada
-- title:
--   Small Hermitian perturbations of the identity are positive: $\mathbb 1 + tH\ge 0$ for some $t>0$
-- statement:
--   Let $H$ be a Hermitian $n\times n$ complex matrix. Then there is a real number $t>0$ such that
--
--   $$\mathbb 1 + t\,H \;\ge\; 0$$
--
--   is positive semidefinite.
--
--   In Appendix C, this fact justifies the step "since the set of matrices $M^{A_1A_2}\ge 0$ is a substantial set, condition (5) can be equivalently imposed on arbitrary matrices of the form (18)". Every Hermitian CJ matrix with the correct partial trace is an affine combination of CJ matrices of CPTP maps, obtained by perturbing the maximally mixed map $\mathbb 1/d_{X_2}$. So a linear normalization condition that holds on all CPTP maps holds on all such Hermitian matrices.
-- source:
--   O. Oreshkov, F. Costa, C. Brukner, Quantum correlations with no causal order, Nat. Commun. 3, 1092 (2012), https://arxiv.org/abs/1105.4464v3, Appendix C, p. 9 ('Since the set of matrices M^{A1A2} >= 0 is a substantial set, condition (5) can be equivalently imposed on arbitrary matrices of the form (18)')

import Mathlib

open Matrix
open scoped ComplexOrder

namespace QInfo

theorem exists_posSemidef_one_add_smul {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) :
    ∃ t : ℝ, 0 < t ∧ (1 + (t : ℂ) • H).PosSemidef := by sorry

end QInfo
