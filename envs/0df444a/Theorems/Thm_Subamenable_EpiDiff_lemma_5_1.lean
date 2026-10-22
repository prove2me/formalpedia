-- Prove2me | Theorems.Thm_Subamenable_EpiDiff_lemma_5_1
-- name    : Subamenable.EpiDiff.lemma_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:14:38.462837+00:00
-- url     : https://prove2.me/theorems/0dfe5afa-3262-4e6a-9143-5cf57b17a9a5
-- title:
--   Lemma 5.1 — parabolic subderivative as a positive-time limit
-- statement:
--   Let $\vartheta$ be convex piecewise linear-quadratic with representation (2.9). For $\bar y\in\operatorname{dom}\vartheta$, $w\in\operatorname{dom}d\vartheta(\bar y)$, and $z\in T^2_{\operatorname{dom}\vartheta}(\bar y,w)$, the parabolic subderivative is the positive-time limit
--
--   $$d^2\vartheta(\bar y)(w;z)=\lim_{t\downarrow0}\frac{\vartheta(\bar y+tw+\tfrac12t^2z)-\vartheta(\bar y)-t\,d\vartheta(\bar y)(w)}{\tfrac12t^2}.$$
--
--   The result permits a fixed second-order direction in place of the perturbations used in the lower-limit definition.
--
--   **Formalization Note** The hypothesis $w\in\operatorname{dom}d\vartheta(\bar y)$ and convex PWLQ assumptions make the first subderivative finite, so the quotient subtracts its real value. The limit is taken in `EReal` along positive times.
-- source:
--   Mohammadi, Mordukhovich, Sarabi, Variational analysis of composite models with applications to continuous optimization, arXiv:1905.08837v2, p. 21, Lemma 5.1, (5.1)

import Mathlib
import Definitions.Def_Subamenable_EpiDiff_Composite

open Filter Topology

namespace Subamenable.EpiDiff

theorem lemma_5_1 {m : ℕ} (theta : E m → EReal) (R : PWLQRep m)
    (hrep : IsPWLQRep theta R) (hconv : IsConvexPWLQ theta)
    (ybar : E m) (hy : ybar ∈ dom theta) (w : E m)
    (hw : w ∈ dom (subderiv theta ybar))
    (z : E m) (hz : z ∈ secondTangentSet (dom theta) ybar w) :
    Tendsto
      (fun t : ℝ =>
        (theta (ybar + t • w + (t ^ 2 / 2) • z) -
          (((theta ybar).toReal + t * (subderiv theta ybar w).toReal : ℝ) : EReal)) *
            ((2 / t ^ 2 : ℝ) : EReal))
      (𝓝[>] (0 : ℝ)) (𝓝 (parabolicSubderiv theta ybar w z)) := by sorry

end Subamenable.EpiDiff
