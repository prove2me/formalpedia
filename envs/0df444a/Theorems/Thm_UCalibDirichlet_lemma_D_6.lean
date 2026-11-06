-- Prove2me | Theorems.Thm_UCalibDirichlet_lemma_D_6
-- name    : UCalibDirichlet.lemma_D_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:25:11.332198+00:00
-- url     : https://prove2.me/theorems/3d92207a-6e18-44c0-9517-8a4710379795
-- title:
--   Lemma D.6 — Bernstein gap on a segment $\le$ multivariate Bernstein gap
-- statement:
--   Let $F:\Delta_K\to\mathbb R$ be convex and $T\ge1$. For $p,v\in\Delta_K$ let $f(x)=F(xp+(1-x)v)$ on $[0,1]$. Then
--   $$\sup_{x\in[0,1]}\Big\{\mathbb E_{S\sim\mathrm{Bin}(T,x)}\big[f(S/T)\big]-f(x)\Big\}\le\sup_{q\in\Delta_K}\Big\{\mathbb E_{M\sim\mathrm{Mult}(T,q)}\big[F(M/T)\big]-F(q)\Big\}.$$
--
--   It transfers scalar Bernstein gaps of the one-dimensional restrictions of $F$ to the multivariate gap that defines $L_F(T)$.
--
--   Differences from the source:
--   - reading: for some p, v ∈ Δ_K → for all p, v ∈ Δ_K; reason: the proof fixes arbitrary p, v and the lemma is applied with p = e_i and random v = R (p.14); 'for any' is the stronger reading
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), Lemma D.6, p.39

import Mathlib
import Definitions.Def_UCalibDirichlet_bern
import Definitions.Def_UCalibDirichlet_multBern

namespace UCalibDirichlet

/-- **Lemma D.6 (Bernstein to multivariate Bernstein).** Frongillo, Luo, Mehta & Schneider
(manuscript, STOC 2027 submission), Lemma D.6, p.39: "Let `F : Δ_K → ℝ` be convex and `T ≥ 1`. For
some `p, v ∈ Δ_K`, let `f : [0, 1] → ℝ` be defined as `f(x) = F(xp + (1 − x)v)`. Then
`sup_{x∈[0,1]} { E_{S∼Bin(T,x)}[f(S/T)] − f(x) } ≤ sup_{q∈Δ_K} { E_{M∼Mult(T,q)}[F(M/T)] − F(q) }`."

**Formalization Note.** "For some `p, v ∈ Δ_K`" is read as "for any `p, v ∈ Δ_K`" (the proof fixes
arbitrary `p, v`, and the lemma is applied with `p = e_i` and `v = R` random, p.14). The
binomial and multinomial expectations are `bern` and `multBern`. Both suprema are real `⨆` of
bounded families (`F` is bounded on the simplex). -/
theorem lemma_D_6 {K : ℕ} (F : (Fin K → ℝ) → ℝ) (hF : ConvexOn ℝ (stdSimplex ℝ (Fin K)) F)
    (T : ℕ) (hT : 1 ≤ T) (p v : Fin K → ℝ) (hp : p ∈ stdSimplex ℝ (Fin K))
    (hv : v ∈ stdSimplex ℝ (Fin K)) :
    (⨆ x : Set.Icc (0 : ℝ) 1,
        (bern (fun y => F (y • p + (1 - y) • v)) T x - F ((x : ℝ) • p + (1 - (x : ℝ)) • v))) ≤
      ⨆ q : stdSimplex ℝ (Fin K), (multBern F T q - F q) := by sorry

end UCalibDirichlet
