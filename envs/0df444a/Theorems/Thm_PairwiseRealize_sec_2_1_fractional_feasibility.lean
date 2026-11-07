-- Prove2me | Theorems.Thm_PairwiseRealize_sec_2_1_fractional_feasibility
-- name    : PairwiseRealize.sec_2_1_fractional_feasibility
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:55:54.967179+00:00
-- url     : https://prove2.me/theorems/dc746a8b-d760-49e8-9921-13877d5a0d5a
-- title:
--   §2.1, p.3 — $v_x=Tw_x$, invertibility of $T$, and fractional feasibility as $y_U\in P_U$
-- statement:
--   With the notation of §2.1:
--
--   1. $v_x=Tw_x$ for every row $x\in V$;
--   2. $T$ is injective on $\mathbb R^m$, hence invertible over the reals;
--   3. for every $U\subseteq V$ and every integer target $b$, the centered vector $y_U$ lies in $P_U$ if and only if $b=\sum_{x\in U}p_xw_x$ for some $p\in[0,1]^U$.
--
--   The third item says that membership in the zonotope is exactly the linear relaxation of the realization problem.
--
--   Differences from the source:
--   - encoding: T is "the fixed invertible integer matrix induced by" the two identities → the explicit formula `Tmap`, with injectivity over ℝ; reason: the page names exactly these identities; T is invertible over ℚ and ℝ, not unimodular
-- source:
--   Shi, Sun, Robust Exact Realization of Pairwise Boolean Statistics, STOC 2027 submission (sha256 62090516…), §2.1, p.3 (PDF p.4), and §A.3, p.13 (PDF p.14)

import Mathlib
import Definitions.Def_PairwiseRealize_Model

namespace PairwiseRealize

/-- **§2.1, p.3 (PDF p.4): the coordinates `v_x = T w_x`, invertibility of `T`, and fractional
feasibility.** K. Shi, H. Sun, *Robust Exact Realization of Pairwise Boolean Statistics*, STOC 2027
submission (manuscript sha256 62090516…), §2.1, printed p.3 (PDF p.4), and §A.3, printed p.13
(PDF p.14): "The feature vectors in (2.1) satisfy v_x = Tw_x, where T is the fixed invertible
integer matrix induced by σᵢ = 2xᵢ − 1 and σᵢσⱼ = 4xᵢxⱼ − 2xᵢ − 2xⱼ + 1." "The zonotope P_U is the
image of the fractional cube [−1, 1]^U under a ↦ Σ_{x∈U} a_x v_x. Thus y_U ∈ P_U is exactly the
fractional-feasibility condition."

1. `v_x = T w_x` for every row `x`;
2. `T` is injective on `ℝ^m` (so invertible);
3. for every `U ⊆ V` and every integer target `b`, `y_U ∈ P_U` if and only if
   `b = Σ_{x∈U} p_x w_x` for some `p ∈ [0, 1]^U`. -/
theorem sec_2_1_fractional_feasibility (n : ℕ) :
    (∀ x : Row n, vvec n x = Tmap n (wvec n x)) ∧
    Function.Injective (Tmap (R := ℝ) n) ∧
    ∀ (U : Finset (Row n)) (b : Feat n → ℤ),
      centered n U b ∈ zonotope n U ↔
        ∃ p : Row n → ℝ, (∀ x ∈ U, p x ∈ Set.Icc (0 : ℝ) 1) ∧
          (fun f => (b f : ℝ)) = ∑ x ∈ U, p x • wR n x := by sorry

end PairwiseRealize
