-- Prove2me | Theorems.Thm_QVolKLS_section_2_4_dyadic_rescaling
-- name    : QVolKLS.section_2_4_dyadic_rescaling
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:37:37.787212+00:00
-- url     : https://prove2.me/theorems/c01f7cec-f734-412c-a802-e4d7ad557bfa
-- title:
--   §2.4 — dyadic rescaling: $B(\tilde x_c,\tilde r)\subseteq K\subseteq B(\tilde x_c,\tilde R)$ and $\tilde R/\tilde r\le 9R/r$
-- statement:
--   Let $K\subseteq\mathbb R^d$, $x_c\in\mathbb R^d$ and $0<r\le R$ with $B(x_c,r)\subseteq K\subseteq B(x_c,R)$.
--
--   1. For every center $\tilde x_c$ with $\|\tilde x_c-x_c\|_2\le r/8$ and all radii
--   $$
--   \tilde r\in[r/4,\,r/2],\qquad \tilde R\in[R+r/8,\ 2(R+r/8)],
--   $$
--   we have $B(\tilde x_c,\tilde r)\subseteq K\subseteq B(\tilde x_c,\tilde R)$ and $\tilde R/\tilde r\le 9R/r$.
--   2. Such a center and such radii can be chosen dyadic (every coordinate of $\tilde x_c$, and $\tilde r$, $\tilde R$, of the form $k/2^p$).
--
--   This lets the volume algorithm assume dyadic center and radii, so that lattice points of the rescaled body are exactly dyadic query points.
--
--   **Formalization Note** Inner balls are open and outer balls closed, as in the main theorem.
--
--   Differences from the source:
--   - generalization: K a convex body with rational data x_c, r, R → K any subset of ℝ^d, x_c any real point, r, R real; reason: the argument uses only the two inclusions; it specializes to the paper's data
--   - reading: choose a dyadic center … and dyadic radii … Then, we have … → two clauses: the conclusion for every admissible center and radii, and the existence of dyadic ones; reason: the sentence asserts both that such choices exist and that any of them works
--   - reading: B(x₀, r) ⊆ K ⊆ B(x₀, R) with B(x, r) not specified open or closed → open inner ball, closed outer ball; reason: the stronger of the readings: an open inner ball and a closed outer ball admit the most bodies
-- source:
--   R. Zhang, Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation, arXiv:2610.04987 (preprint, held version, sha256 eee7a45e7117af08035a8d75fd6f145fa82ddade51ad87a6507911b6a0aa4f80), §2.4 (Dyadic rescaling), p.24

import Definitions.Def_QVolKLS_IsConvexBody

set_option autoImplicit false

namespace QVolKLS

/-- R. Zhang, arXiv:2610.04987 (held version, sha256 eee7a45e…), **§2.4, "Dyadic rescaling"**,
p.24: if `B(x_c, r) ⊆ K ⊆ B(x_c, R)` with `0 < r ≤ R`, then every center `x̃_c` with
`‖x̃_c − x_c‖₂ ≤ r/8` and radii `r̃ ∈ [r/4, r/2]`, `R̃ ∈ [R + r/8, 2(R + r/8)]` satisfy
`B(x̃_c, r̃) ⊆ K ⊆ B(x̃_c, R̃)` and `R̃/r̃ ≤ 9R/r`; and such a center and such radii can be chosen
dyadic.

**Formalization Note.** `K` is any subset of `ℝ^d`; the inner balls are open and the outer balls
closed, as in the main theorem. "Dyadic" means `k/2^p` with `k ∈ ℤ`, `p ∈ ℕ` (each coordinate for the
center). -/
theorem section_2_4_dyadic_rescaling (d : ℕ) (K : Set (Euc d)) (xc : Euc d) (r R : ℝ)
    (hr : 0 < r) (hrR : r ≤ R) (hin : Metric.ball xc r ⊆ K)
    (hout : K ⊆ Metric.closedBall xc R) :
    (∀ (xt : Euc d) (rt Rt : ℝ), ‖xt - xc‖ ≤ r / 8 → r / 4 ≤ rt → rt ≤ r / 2 →
        R + r / 8 ≤ Rt → Rt ≤ 2 * (R + r / 8) →
        Metric.ball xt rt ⊆ K ∧ K ⊆ Metric.closedBall xt Rt ∧ Rt / rt ≤ 9 * R / r) ∧
    (∃ (xt : Euc d) (rt Rt : ℝ), (∀ j, IsDyadic (xt j)) ∧ IsDyadic rt ∧ IsDyadic Rt ∧
        ‖xt - xc‖ ≤ r / 8 ∧ r / 4 ≤ rt ∧ rt ≤ r / 2 ∧ R + r / 8 ≤ Rt ∧
        Rt ≤ 2 * (R + r / 8)) := by sorry

end QVolKLS
