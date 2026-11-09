-- Prove2me | Theorems.Thm_RecGaussColoring_Main_lemma_2_4
-- name    : RecGaussColoring.Main.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:24:26.238339+00:00
-- url     : https://prove2.me/theorems/48b7393a-2ea4-41c1-afe8-dcc28522ab98
-- title:
--   Lemma 2.4 — lower tail of a Gaussian maximum
-- statement:
--   Let $Y=(y_1,\ldots,y_N)$ be a finite indexed family in $\mathbb R^d$, with every norm at most one. Fix $t>0$, $T>t$, and $L>0$. Set $M_Y(\gamma)=\max_r\langle\gamma,y_r\rangle$, $p=\Pr[M_Y>t]$, and $\delta=N\Phi^c(T)$. If $0<\delta<1$, then
--   $$
--   \Pr[M_Y\le t-L]\le
--   \begin{cases}1,&p=0,\\
--   \Phi\bigl((1+L/(T-t))\Phi^{-1}(1-p)-(L/(T-t))\Phi^{-1}(1-\delta)\bigr),&p\ne0.
--   \end{cases}
--   $$
--   This controls the lower tail using an upper-tail probability and family size. The assumption on $\delta$ excludes $N=0$, while repetitions in $Y$ remain allowed.
--
--   Differences from the source:
--   - encoding: finite Euclidean families and labelled finite graphs → Fin n vertices and EuclideanSpace ℝ (Fin d); reason: relabelling preserves every finite instance and dimension
--   - encoding: Φ(+∞)=1 when all vectors vanish and p=0 → an explicit p=0 branch returning one, with no extra positivity hypothesis on p; reason: this retains the source proof’s first case and avoids extended-real arithmetic; otherwise 0<p<1 follows from t>0 and a nonzero vector
-- source:
--   Ijay Narang, Yukai Tang, STOC 2027 submission #295 (October 2026), Lemma 2.4, p. 8. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/295.pdf

import Definitions.Def_RecGaussColoring_Main_Gaussian

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open scoped Topology
noncomputable section

namespace RecGaussColoring.Main

/-- Lemma 2.4, p. 8; lowerTailBound retains the all-zero family case. -/
theorem lemma_2_4 (d N : ℕ) (Y : Fin N → Space d)
    (hY : ∀ r, ‖Y r‖ ≤ 1) (t T L : ℝ)
    (ht : 0 < t) (hT : t < T) (hL : 0 < L)
    (hδ0 : 0 < (N : ℝ)*PhiTail T) (hδ1 : (N : ℝ)*PhiTail T < 1) :
  gaussProb (maxLowerEvent Y (t-L)) ≤
    lowerTailBound (maxUpperProb Y t) ((N : ℝ)*PhiTail T) t T L := by sorry

end RecGaussColoring.Main
