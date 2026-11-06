-- Prove2me | Theorems.Thm_SilverRateSC_lemma_A_2
-- name    : SilverRateSC.lemma_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:46:46.869267+00:00
-- url     : https://prove2.me/theorems/9af19165-fbd1-46e4-b9f8-1997629b0c05
-- title:
--   Lemma A.2 — the gap trajectory on the circular arc
-- statement:
--   Fix $\kappa\ge4$, $0<\beta\le1/4$, $\ell_i\ge0$, and nonnegative gap stepsizes $h_1,\dots,h_{m_{\rm gap}}$ with $s_i/\kappa\le1/16$, where $s_i=\sum_jh_j$. Let $R=1+\beta$, $c_\beta=\beta+\sqrt{1+2\beta}$, and let $K$ be the convex hull of the origin and the shorter arc of the circle with centre $(\beta,\beta)$ and radius $R$ joining $(c_\beta,0)$ to $(\beta,-1)$.
--
--   For every $\rho>0$ there exist $\tau\ge1$, points $r_0,\dots,r_{m_{\rm gap}}$ and vectors $v_0,\dots,v_{m_{\rm gap}}$ on the arc such that
--   $$r_j+\frac{z^\circ}\rho=\Bigl(1-\frac{h_j}\kappa\Bigr)\Bigl(r_{j-1}+\frac{z^\circ}\rho\Bigr)-\frac{(1-1/\kappa)h_j}2v_{j-1}\quad(1\le j\le m_{\rm gap}),\qquad \frac{z^\circ}\rho=\Bigl(\frac{\ell_i}\rho+\frac\tau\beta,\ \tau\Bigr),$$
--   $r_{m_{\rm gap}}=v_{m_{\rm gap}}=(\beta,-1)$, $r_0$ has second coordinate $-\tau$, and $v_j=\Pi_K(r_j)$, $r_j\in[\beta,\infty)\times[-\tau,-1]$ for $0\le j\le m_{\rm gap}$. Let $P$ be the first coordinate of
--   $$\frac{1-1/\kappa}2\sum_{j=1}^{m_{\rm gap}}h_j\Bigl[\prod_{l=j+1}^{m_{\rm gap}}\Bigl(1-\frac{h_l}\kappa\Bigr)\Bigr]v_{j-1}.$$
--   Then
--   $$P\le\frac{1-1/\kappa}2c_\beta s_i,\qquad \tau\le1+\frac{1-1/\kappa}2s_i,\qquad \tau\le\beta\exp\Bigl[\frac{\sqrt2R-\beta}\beta\Bigr].$$
--   Moreover, $\tau$ and $P$ can be chosen as continuous functions of $\rho$.
--
--   This backward trajectory is the scaled gap trajectory of the bending component; the bounds on $P$ and $\tau$ produce the constants $c_\beta$ and $a_\beta$ of Lemma 3.1.
--
--   Differences from the source:
--   - encoding: τ and P can be chosen as continuous functions of ρ → ∃ τ P : ℝ → ℝ continuous on (0,∞) such that for every ρ > 0 the points exist with τ ρ and P ρ; reason: literal meaning of the clause
--   - encoding: gap stepsizes h_1, …, h_{m_gap}; points r_j, v_j for 0 ≤ j ≤ m_gap → a list hs with h_j = hs.getD (j−1) 0; sequences r v : ℕ → ℝ² constrained for j ≤ hs.length; reason: same data; entries beyond m_gap are unconstrained and unused
--   - encoding: v_j on the arc, Π_K → v j ∈ arcPts β, OrabonaOL.OGD.IsEuclideanProj (arcK β); reason: the arc's points (p,q) with p ≥ β, −1 ≤ q ≤ 0; the projection onto a nonempty closed convex set is unique
--   - encoding: points and vectors of ℝ² with their coordinates → EuclideanSpace ℝ (Fin 2), coordinate 0 first, vectors written !₂[·, ·]; reason: Lean representation; same objects
-- source:
--   Liu, Ye, Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case, arXiv:2609.26873 (sha256 1e325f28…), Lemma A.2, p.30; setting §A.1, p.29

import Mathlib
import Definitions.Def_SilverRateSC_arcK
import Definitions.Def_OrabonaOL_OGD_IsEuclideanProj

namespace SilverRateSC

/-- **Lemma A.2 (Gap trajectory).** Fix `κ ≥ 4`, `0 < β ≤ 1/4`, `ℓ_i ≥ 0`, and nonnegative gap
stepsizes `h_1, …, h_{m_gap}` with `s_i/κ ≤ 1/16`, `s_i = ∑ h_j`; let `K` be the convex hull of the
origin and the shorter arc of the circle with center `(β, β)`, radius `R = 1 + β`, joining
`(c_β, 0)` to `(β, −1)`. For every `ρ > 0`, there exist `τ ≥ 1`, points `r_0, …, r_{m_gap}` and
vectors `v_0, …, v_{m_gap}` on the arc satisfying (32),
`r_j + z°/ρ = (1 − h_j/κ)(r_{j−1} + z°/ρ) − ((1 − 1/κ)h_j/2) v_{j−1}` (`1 ≤ j ≤ m_gap`),
`z°/ρ = (ℓ_i/ρ + τ/β, τ)`, such that `r_{m_gap} = v_{m_gap} = (β, −1)`, `r_0` has second
coordinate `−τ`, and `v_j = Π_K(r_j)`, `r_j ∈ [β, ∞) × [−τ, −1]` (`0 ≤ j ≤ m_gap`). Let `P` be
the first coordinate of `((1 − 1/κ)/2) ∑_{j=1}^{m_gap} h_j [∏_{l=j+1}^{m_gap} (1 − h_l/κ)] v_{j−1}`
(33). Then `P ≤ ((1 − 1/κ)/2) c_β s_i`, `τ ≤ 1 + ((1 − 1/κ)/2) s_i`,
`τ ≤ β exp[(√2 R − β)/β]`. Moreover, `τ` and `P` can be chosen as continuous functions of `ρ`.

Liu, Ye, *Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case*,
arXiv:2609.26873, Lemma A.2, p. 30 (setting §A.1, p. 29).

**Formalization Note** The gap stepsizes are the list `hs`, `h_j = hs.getD (j − 1) 0`,
`m_gap = hs.length`. "Continuous functions of `ρ`" is encoded as functions `τ, P : ℝ → ℝ`
continuous on `(0, ∞)` such that for each `ρ > 0` the points exist with `τ ρ` and `P ρ`. "On the
arc" is membership in `arcPts β`, `Π_K` is `OrabonaOL.OGD.IsEuclideanProj (arcK β)`. The standing
`0 ≤ h_j < κ` of §3 follows from `h_j ≥ 0` and `s_i/κ ≤ 1/16`. -/
theorem lemma_A_2 (κ β ℓ : ℝ) (hs : List ℝ) (hκ : 4 ≤ κ) (hβ0 : 0 < β) (hβ : β ≤ 1 / 4)
    (hℓ : 0 ≤ ℓ) (hh : ∀ h ∈ hs, 0 ≤ h) (hsκ : hs.sum / κ ≤ 1 / 16) :
    ∃ τ P : ℝ → ℝ, ContinuousOn τ (Set.Ioi 0) ∧ ContinuousOn P (Set.Ioi 0) ∧
      ∀ ρ : ℝ, 0 < ρ → 1 ≤ τ ρ ∧
        ∃ r v : ℕ → EuclideanSpace ℝ (Fin 2),
          (∀ j ∈ Finset.Icc 1 hs.length,
            r j + !₂[ℓ / ρ + τ ρ / β, τ ρ] =
              (1 - hs.getD (j - 1) 0 / κ) • (r (j - 1) + !₂[ℓ / ρ + τ ρ / β, τ ρ]) -
                ((1 - 1 / κ) * hs.getD (j - 1) 0 / 2) • v (j - 1)) ∧
          r hs.length = !₂[β, -1] ∧ v hs.length = !₂[β, -1] ∧ r 0 1 = -τ ρ ∧
          (∀ j ≤ hs.length, v j ∈ arcPts β ∧ OrabonaOL.OGD.IsEuclideanProj (arcK β) (r j) (v j) ∧
            β ≤ r j 0 ∧ -τ ρ ≤ r j 1 ∧ r j 1 ≤ -1) ∧
          P ρ = (1 - 1 / κ) / 2 * ∑ j ∈ Finset.Icc 1 hs.length,
            hs.getD (j - 1) 0 * (∏ l ∈ Finset.Ioc j hs.length, (1 - hs.getD (l - 1) 0 / κ)) *
              v (j - 1) 0 ∧
          P ρ ≤ (1 - 1 / κ) / 2 * cBeta β * hs.sum ∧
          τ ρ ≤ 1 + (1 - 1 / κ) / 2 * hs.sum ∧
          τ ρ ≤ β * Real.exp ((Real.sqrt 2 * RBeta β - β) / β) := by sorry

end SilverRateSC
