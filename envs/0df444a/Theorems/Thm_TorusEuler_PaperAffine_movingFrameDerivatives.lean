-- Prove2me | Theorems.Thm_TorusEuler_PaperAffine_movingFrameDerivatives
-- name    : TorusEuler.PaperAffine.movingFrameDerivatives
-- status  : Open
-- author  : @LG
-- created : 2026-11-20T19:40:15.248142+00:00
-- url     : https://prove2.me/theorems/b570d14e-0270-4a11-9c4f-f8d1925159d6
-- title:
--   Lemma 2.2 — the moving frame of a wave and its derivative equations
-- statement:
--   **Lemma 2.2 of the frozen manuscript (cc:lem:frame).** Let $B(t)$ be a trace-free matrix on an interval $J$, and let $k(t)\ne0$, $a(t)\ne0$ satisfy the Craik–Criminale equations (`WaveOn`) with background $B$, with $k(t)\cdot a(t)=0$ on $J$. Let $(E_1,E_2,E_3)$ be the moving frame $E_1=k/\|k\|$, $E_2=a/\|a\|$, $E_3=E_1\times E_2$ (`frame k a`), and write $B_{ij}=E_i\cdot B E_j$ (`entry`, zero-based). Then the frame is orthonormal at every $t\in J$, and, with derivatives taken within $J$,
--   $$E_1'=-B_{12}E_2-B_{13}E_3,\qquad E_2'=B_{12}E_1-B_{32}E_3,\qquad E_3'=B_{13}E_1+B_{32}E_2,$$
--   and the strength $\sigma=\|k\|\,\|a\|$ satisfies $(\log\sigma)'=B_{33}$.
--
--   Only $\operatorname{tr}B=0$ is used; no symmetry of $B'+B^2$ is required. These equations identify the couplings $\nu=B_{12}$ and $\eta=B_{32}$ that drive the amplification of the next wave over the preceding one.
--
--   **Formalization Note** Indices are zero-based: `entry e B 0 1` is $B_{12}$, `entry e B 2 1` is $B_{32}$, `entry e B 2 2` is $B_{33}$. Orthonormality of the frame is an explicit conclusion.
-- source:
--   Alpöge–Buckmaster–Coiculescu, *Finite-Time Singularity Formation for the Three-Dimensional Euler Equations*, frozen manuscript of 18 November 2026 (torus-paper-freeze-2026-11-18). Lean: https://github.com/mcoiculescu/EulerBlowupPublic/blob/36d3961161f8e7bba9cc8f671e5d0c4a27281239/formalization/lean/TorusEuler/PaperAffineStatements.lean#L50; TeX: https://github.com/mcoiculescu/EulerBlowupPublic/blob/36d3961161f8e7bba9cc8f671e5d0c4a27281239/frozen-manuscript/sections/02_affine.tex#L59 (cc:lem:frame, cc:eq:frame).

import Mathlib
import Definitions.Def_TorusEuler_Statement
import Definitions.Def_TorusEuler_Affine

open Set
open scoped InnerProductSpace
open TorusEuler.MovingWaveVector

namespace TorusEuler.PaperAffine

/-- Lemma 2.2, `cc:lem:frame`. The normalized moving frame, its
three derivatives, and the logarithmic-strength derivative. -/
theorem movingFrameDerivatives {J : Set ℝ} {B : ℝ → Vec3 →L[ℝ] Vec3} {k a : ℝ → Vec3}
    (htr : ∀ t ∈ J, LinearMap.trace ℝ Vec3 (B t).toLinearMap = 0)
    (hWave : WaveOn J B k a)
    (hData : ∀ t ∈ J, k t ≠ 0 ∧ a t ≠ 0 ∧ ⟪k t, a t⟫_ℝ = 0) :
    let e := frame k a
    ∀ t ∈ J, Orthonormal ℝ (e t) ∧
      HasDerivWithinAt (fun u => e u 0)
        (-(entry (e t) (B t) 0 1) • e t 1 - entry (e t) (B t) 0 2 • e t 2) J t ∧
      HasDerivWithinAt (fun u => e u 1)
        (entry (e t) (B t) 0 1 • e t 0 - entry (e t) (B t) 2 1 • e t 2) J t ∧
      HasDerivWithinAt (fun u => e u 2)
        (entry (e t) (B t) 0 2 • e t 0 + entry (e t) (B t) 2 1 • e t 1) J t ∧
      HasDerivWithinAt (fun u => Real.log (‖k u‖ * ‖a u‖)) (entry (e t) (B t) 2 2) J t := by sorry

end TorusEuler.PaperAffine
