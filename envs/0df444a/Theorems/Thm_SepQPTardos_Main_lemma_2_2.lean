-- Prove2me | Theorems.Thm_SepQPTardos_Main_lemma_2_2
-- name    : SepQPTardos.Main.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:12:12.671748+00:00
-- url     : https://prove2.me/theorems/3112c9e7-12c1-4327-9f65-49c9b50a0910
-- title:
--   Lemma 2.2 — separable exchange inequality
-- statement:
--   Let $\psi(u)=\sum_{e=1}^m\psi_e(u_e)$ where every $\psi_e:\mathbb R\to\mathbb R$ is convex, and let $v,w,h\in\mathbb R^m$. If $h$ is conformal to $w-v$ and $|h_e|\le|w_e-v_e|$ for every $e$, then
--
--   $$\psi(v+h)+\psi(w-h)\le\psi(v)+\psi(w).\tag{9}$$
--
--   Exchanging a conformal piece of the displacement between two points therefore never increases the total objective; this drives the two-sided proximity bound of Lemma 3.2.
--
--   Differences from the source:
--   - encoding: ψ(u) = Σ_e ψ_e(u_e) separable convex → ψ_e : ℝ → ℝ convex on ℝ, vectors indexed by Fin m; reason: finite-valued separable convex functions; the paper applies the lemma to separable convex quadratics
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, STOC 2027 submission #829 (October 2026), §2.3, Lemma 2.2, eq. (9), p. 6

import Mathlib
import Definitions.Def_SepQPTardos_Main_Circuits

namespace SepQPTardos.Main

/-- Lemma 2.2 (separable exchange; Cui–Li–Miao, STOC 2027 #829, p. 6): let
`ψ(u) = ∑ₑ ψₑ(uₑ)` with every `ψₑ : ℝ → ℝ` convex. If `h` is conformal to `w − v` and
`|hₑ| ≤ |wₑ − vₑ|` for all `e`, then `ψ(v + h) + ψ(w − h) ≤ ψ(v) + ψ(w)` (eq. (9)). -/
theorem lemma_2_2 {m : ℕ} (ψ : Fin m → ℝ → ℝ) (hψ : ∀ e, ConvexOn ℝ Set.univ (ψ e))
    (v w h : Fin m → ℝ) (hconf : Conformal h (w - v)) (hle : ∀ e, |h e| ≤ |w e - v e|) :
    ∑ e, ψ e (v e + h e) + ∑ e, ψ e (w e - h e) ≤ ∑ e, ψ e (v e) + ∑ e, ψ e (w e) := by sorry

end SepQPTardos.Main
