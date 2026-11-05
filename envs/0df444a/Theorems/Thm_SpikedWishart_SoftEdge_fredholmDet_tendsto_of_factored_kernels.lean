-- Prove2me | Theorems.Thm_SpikedWishart_SoftEdge_fredholmDet_tendsto_of_factored_kernels
-- name    : SpikedWishart.SoftEdge.fredholmDet_tendsto_of_factored_kernels
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-04T09:06:03.195563+00:00
-- url     : https://prove2.me/theorems/bc104ba9-c5eb-41d2-9972-30dd82844b4d
-- title:
--   Fredholm determinants of product kernels $\int_0^\infty H_i(u+y)J_i(v+y)dy$ converge under exponential-weight uniform convergence
-- statement:
--   Let $H_i,J_i,H,J:\mathbb R\to\mathbb C$, $C\ge0$, $c>0$, $x\in\mathbb R$ and $\delta_i\to0$ with eventually $0\le\delta_i\le1$. Suppose that for all $w\ge x$, $|H(w)|,|J(w)|\le Ce^{-cw}$, eventually $|H_i(w)-H(w)|,|J_i(w)-J(w)|\le Ce^{-cw}\delta_i$, and eventually $H_i,J_i$ are continuous. Then
--
--   $$\det\Big(1-\mathrm{Re}\int_0^\infty H_i(\cdot+y)J_i(\cdot+y)\,dy\Big)_{L^2((x,\infty))}\longrightarrow\det\Big(1-\mathrm{Re}\int_0^\infty H(\cdot+y)J(\cdot+y)\,dy\Big)_{L^2((x,\infty))},$$
--
--   the determinants being the Fredholm series.
--
--   Role: this is the continuity step that turns the convergence of $\mathcal H,\mathcal J$ in Proposition 3.1 into the convergence of the Fredholm determinants in the proof of Theorem 1.1.
-- source:
--   J. Baik, G. Ben Arous and S. Peche, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), https://doi.org/10.1214/009117905000000233, proof of Theorem 1.1, Section 3, p. 1664 (convergence of the Fredholm determinants from (123)-(124)); B. Simon, Trace Ideals and Their Applications, 2nd ed., AMS 2005, Theorem 3.4 (continuity of the Fredholm determinant); G. W. Anderson, A. Guionnet and O. Zeitouni, An Introduction to Random Matrices, Cambridge 2010, Lemma 3.4.5

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Airy
open MeasureTheory

namespace SpikedWishart.SoftEdge

theorem fredholmDet_tendsto_of_factored_kernels (Hn Jn : ℕ → ℝ → ℂ) (Hi Ji : ℝ → ℂ) (δ : ℕ → ℝ) (C c x : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hδ1 : ∀ᶠ i in Filter.atTop, 0 ≤ δ i ∧ δ i ≤ 1)
    (hHn : ∀ᶠ i in Filter.atTop, ∀ w, x ≤ w → ‖Hn i w - Hi w‖ ≤ C * Real.exp (-c * w) * δ i)
    (hJn : ∀ᶠ i in Filter.atTop, ∀ w, x ≤ w → ‖Jn i w - Ji w‖ ≤ C * Real.exp (-c * w) * δ i)
    (hHi : ∀ w, x ≤ w → ‖Hi w‖ ≤ C * Real.exp (-c * w))
    (hJi : ∀ w, x ≤ w → ‖Ji w‖ ≤ C * Real.exp (-c * w))
    (hHc : ∀ᶠ i in Filter.atTop, Continuous (Hn i))
    (hJc : ∀ᶠ i in Filter.atTop, Continuous (Jn i)) :
    Filter.Tendsto
      (fun i => fredholmDet (fun u v => (∫ y in Set.Ioi (0 : ℝ), Hn i (u + y) * Jn i (v + y)).re) x)
      Filter.atTop
      (nhds (fredholmDet (fun u v => (∫ y in Set.Ioi (0 : ℝ), Hi (u + y) * Ji (v + y)).re) x)) := by sorry

end SpikedWishart.SoftEdge
