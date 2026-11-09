-- Prove2me | Theorems.Thm_WeightedSpectralSketch_LowerBound_tv_le_leverage
-- name    : WeightedSpectralSketch.LowerBound.tv_le_leverage
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:01:57.803726+00:00
-- url     : https://prove2.me/theorems/aaa68a77-39b4-4c5a-a98c-41d2ae4022c0
-- title:
--   Lemma 4.4 — TV distance of the sketches is bounded by the weighted leverage
-- statement:
--   Fix a sketch matrix $A=[a_e]_{e\in E}\in\mathbb R^{N\times E}$, positive base weights $(w_e)_{e\in E}$ and a query coordinate $q\in E$ (in the source: a fixed sketch matrix and a fixed realization of the permutation $\pi$, which determines $w$ and $q$). Under No the input is $\tilde w_e=w_eZ_e$ with independent noises $Z_e$ of density (4); under Yes it is $\tilde w_e=w_eZ_e+\mathbf 1\{e=q\}$. Then
--
--   $$
--   \mathrm{TV}\big((A\tilde w)_{\pi,\mathrm{Yes}},(A\tilde w)_{\pi,\mathrm{No}}\big)\le\sqrt{\min\big\{1,\ 10\,\mathrm{lev}_{a_q}\big((A\,\mathrm{diag}(w))_{-q}\big)\big\}} .
--   $$
--
--   The factor $10$ is inside the square root; it is twice the derivative energy $\int|u'|^2=10$ of the square-root noise density, halved by Lemma 4.3. The bound is the statistical half of the reduction to leverage scores.
--
--   **Formalization Note.** TV is the published `FoundationsRL.DECLower.tvDist`. The leverage is in $[0,\infty]$; after truncation at $1$ it is converted to a real number.
--
--   Differences from the source:
--
--   - generalization: the ring coordinates binom(R,2) with base weights (3) under a fixed π, and the query edge q → any finite coordinate set E, any strictly positive weights w and any coordinate q; reason: the ring base weights are strictly positive, so the source's statement is the instance E = binom(R,2), w = base weights, q = query edge
-- source:
--   Chen, Chen and Yang, A Tight Superlinear Lower Bound on the Sketching Dimension of Weighted Spectral Sparsification, STOC 2027 submission #109 (2026), pinned preprint SHA-256 94f9d972f8c75c577e7195e080b6ed59e722471145d40426a2f0c92315be9f44, p. 12, Lemma 4.4, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/109.pdf

import Mathlib
import Definitions.Def_FoundationsRL_DECLower_tvDist
import Definitions.Def_WeightedSpectralSketch_LowerBound_Leverage
import Definitions.Def_WeightedSpectralSketch_LowerBound_Stat

open MeasureTheory Matrix
open scoped ENNReal

namespace WeightedSpectralSketch.LowerBound

/-- Lemma 4.4, p. 12: for a fixed sketch matrix `A`, fixed positive base weights `w` and a fixed
query coordinate `q` (i.e. a fixed realization of `π`),
`TV((A w̃)_{π,Yes}, (A w̃)_{π,No}) ≤ √(min{1, 10 lev_{a_q}((A diag(w))_{-q})})`, where under No
`w̃_e = w_e Z_e` with independent noises of density (4), and Yes adds `1` to coordinate `q`. -/
theorem tv_le_leverage {E : Type*} [Fintype E] [DecidableEq E] {N : ℕ} (A : Matrix (Fin N) E ℝ)
    (w : E → ℝ) (hw : ∀ e, 0 < w e) (q : E) :
    FoundationsRL.DECLower.tvDist (sketchLaw A w (Pi.single q 1)) (sketchLaw A w 0) ≤
      Real.sqrt
        (min 1 (10 * lev (fun e : {e : E // e ≠ q} => w e.1 • Aᵀ e.1) (Aᵀ q))).toReal := by sorry

end WeightedSpectralSketch.LowerBound
