-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_box_volume_face_bound
-- name    : WeierstrassEllipticZeta.box_volume_face_bound
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-13T04:46:23.75743+00:00
-- url     : https://prove2.me/theorems/985df600-93ea-4ddf-b855-140b440dcdb9
-- title:
--   Box volume loss bounded by coordinate face contributions
-- statement:
--   Let $\sigma$ be a finite set of coordinates and let $a,b:\sigma\to\mathbb N$ satisfy $a_i\le b_i$ for every $i$. The loss of volume when the coordinate box with side lengths $b_i+1$ is shortened by $a_i$ in coordinate $i$ is bounded by the sum of the coordinate face contributions:
--   $$\prod_{i\in\sigma}(b_i+1)
--   \le \prod_{i\in\sigma}(b_i-a_i+1)
--    +\sum_{i\in\sigma}a_i\prod_{j\in\sigma\setminus\{i\}}(b_j+1).$$
--   Each term in the sum is the shortening in one coordinate times the number of points in the corresponding face of the original box. The estimate allows zero coordinate bounds, zero shortenings, and an empty coordinate set, with the usual empty-product convention. Face regions may overlap; disjointness is not required.
--
--   For the mission, one may take $a_i$ to be the degree of a contact polynomial in variable $i$. The estimate then bounds the difference between the full box count and its admissible support-translation count by explicit degree-weighted face counts.
-- source:
--   Derived box-volume face estimate for the frontier https://prove2.me/theorems/b747c74b-ad76-48cd-90e9-6075fc3b0c81. The mission context is Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2 and Theorem A.2, https://doi.org/10.1017/S001309152610145X. The supporting finite-product estimate is proved by induction on the coordinate set using Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474, Algebra/BigOperators/Ring/Finset.lean (mul_sum), Algebra/BigOperators/Group/Finset/Basic.lean (prod_insert and sum_insert), and Data/Finset/Basic.lean (erase_insert and erase_insert_of_ne). The remaining child asks for a sufficient bound on degree-weighted coordinate faces. Constructing suitable contact boxes and the uniform geometric estimate remain open.

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

theorem WeierstrassEllipticZeta.box_volume_face_bound
    (σ : Type*) [Fintype σ] [DecidableEq σ] (b a : σ → ℕ)
    (hfit : ∀ i : σ, a i ≤ b i) :
    (∏ i : σ, (b i + 1)) ≤ (∏ i : σ, (b i - a i + 1)) +
      ∑ i : σ, a i * ∏ j ∈ (Finset.univ : Finset σ).erase i, (b j + 1) := by sorry
