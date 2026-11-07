-- Prove2me | Theorems.Thm_PairwiseRealize_sec_A_3_support_step
-- name    : PairwiseRealize.sec_A_3_support_step
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:55:45.034213+00:00
-- url     : https://prove2.me/theorems/6cc42584-d101-429c-b20f-38930a316ee6
-- title:
--   §A.3, p.13 — interior depth survives the baseline: $y_U\in t_R+P_{U\setminus R}$, and the residual LP respects unit capacities
-- statement:
--   Let $R\subseteq U$ with $|R|\le L$ and $G=\sum_{x\in R}v_xv_x^{\mathsf T}\preceq2LI_m$. Let $F_0:V\to\{0,1\}$ be a baseline and $t_R=\sum_{x\in R}(2F_0(x)-1)v_x$ its signed Walsh vector. If $y_U+4LB_m\subseteq P_U$ for the centered vector $y_U$ of an integer target $b$, then:
--
--   1. $y_U\in t_R+P_{U\setminus R}$;
--   2. $b=\sum_{x\in R}F_0(x)w_x+\sum_{x\in U\setminus R}p_xw_x$ for some $p\in[0,1]^{U\setminus R}$.
--
--   So after fixing the reserve at its baseline, the fractional problem on the remaining rows is still feasible, with the original unit capacities.
--
--   Differences from the source:
--   - generalization: L = |R| → |R| ≤ L; reason: the page sets L = |R|, which is the case of equality
-- source:
--   Shi, Sun, Robust Exact Realization of Pairwise Boolean Statistics, STOC 2027 submission (sha256 62090516…), §A.3, p.13 (PDF p.14); §3.3, p.8 (PDF p.9)

import Mathlib
import Definitions.Def_PairwiseRealize_Model

namespace PairwiseRealize

/-- **Interior depth survives the baseline, §A.3 p.13 (PDF p.14); §3.3 p.8 (PDF p.9).** K. Shi,
H. Sun, *Robust Exact Realization of Pairwise Boolean Statistics*, STOC 2027 submission (manuscript
sha256 62090516…): "On the spectral event and after the disjointness check, the reserve R ⊆ U
satisfies Σ_{x∈R} |⟨z, v_x⟩| ≤ √L √(zᵀGz) ≤ √2 L‖z‖ ≤ 2L‖z‖. Its baseline signed Walsh vector t_R
has norm at most 2L as well. Consequently Z_R = t_R + Σ_{x∈U∖R} [−v_x, v_x],
h_{Z_R}(z) ≥ h_{P_U}(z) − 4L‖z‖. If y_U + 4LB_m ⊆ P_U, then for every z, ⟨z, y_U⟩ ≤
h_{P_U}(z) − 4L‖z‖ ≤ h_{Z_R}(z). The support-function criterion gives y_U ∈ Z_R. To return
explicitly to the original variables, write y_U = t_R + Σ_{x∈U∖R} a_x v_x with a_x ∈ [−1, 1], and put
p_x = (a_x + 1)/2. If F0 is the reserved binary baseline, […] b = Σ_{x∈R} F0(x)w_x +
Σ_{x∈U∖R} p_x w_x."

Let `R ⊆ U` be sets of rows with `|R| ≤ L`, let `G = Σ_{x∈R} v_x v_xᵀ` satisfy `G ⪯ 2L I_m`, let
`F0 : V → {0,1}` be a baseline and `t_R = Σ_{x∈R} (2F0(x) − 1) v_x` its signed Walsh vector. If
`y_U + 4L B_m ⊆ P_U` for the centered target `y_U` of an integer target `b`, then
1. `y_U ∈ t_R + P_{U∖R}`, and
2. `b = Σ_{x∈R} F0(x) w_x + Σ_{x∈U∖R} p_x w_x` for some `p ∈ [0, 1]^{U∖R}`.

**Formalization Note** The page sets `L = |R|`; the argument needs only `|R| ≤ L`, which is the
form stated (it contains `L = |R|`). `B_m` is the closed Euclidean unit ball. -/
theorem sec_A_3_support_step (n : ℕ) (U R : Finset (Row n)) (hRU : R ⊆ U) (L : ℝ)
    (hRL : (R.card : ℝ) ≤ L)
    (hG : ((2 * L) • (1 : Matrix (Feat n) (Feat n) ℝ) -
      ∑ x ∈ R, Matrix.vecMulVec (vR n x) (vR n x)).PosSemidef)
    (F0 : Row n → Bool) (b : Feat n → ℤ)
    (hball : Metric.closedBall (centered n U b) (4 * L) ⊆ zonotope n U) :
    let tR : EuclideanSpace ℝ (Feat n) := ∑ x ∈ R, (2 * (bv (F0 x) : ℝ) - 1) • vE n x
    (∃ y ∈ zonotope n (U \ R), centered n U b = tR + y) ∧
    ∃ p : Row n → ℝ, (∀ x ∈ U \ R, p x ∈ Set.Icc (0 : ℝ) 1) ∧
      (fun f => (b f : ℝ)) = ∑ x ∈ R, (bv (F0 x) : ℝ) • wR n x + ∑ x ∈ U \ R, p x • wR n x := by sorry

end PairwiseRealize
