-- Prove2me | Theorems.Thm_PriceCapacities_LowerBound_lemma_10_6
-- name    : PriceCapacities.LowerBound.lemma_10_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:23:12.93922+00:00
-- url     : https://prove2.me/theorems/b129d619-b3ec-4f78-9221-fbdefadce04a
-- title:
--   Lemma 10.6 — a weighted absolute-projection pattern that no $cN/d^2$ vectors approximate within $c/\sqrt{Nd^3}$ on average
-- statement:
--   There are absolute constants $c>0$ and $d_0$ such that, for every even $d\ge d_0$, there are weights $1<\omega_x<2$ ($x\in G$) for which
--   $$\Phi(\theta)=\frac1N\sum_{x\in G}\omega_x|\langle\theta,x\rangle|$$
--   has the following property: for every $m\le cN/d^2$ and every $y_1,\dots,y_m\in\mathbb R^d$,
--   $$\frac1N\sum_{\theta\in G}\Big|\Phi(\theta)-\sum_{r=1}^m|\langle\theta,y_r\rangle|\Big|\ \ge\ \frac{c}{\sqrt{Nd^3}} .$$
--   Here $G$ is the pattern set (one vector of each opposite pair among the vectors with coordinates $\pm1/\sqrt d$) and $N=|G|=2^{d-1}$. The lemma says that the projection pattern $\Phi$ cannot be reproduced by few vectors; it is what forces every group of the hard instance to contain many coreset points.
--
--   Differences from the source:
--
--   - encoding: G: one vector from each opposite pair → the representatives with positive first coordinate (PatternIdx, patternVec); reason: Φ, |⟨θ, y⟩| and the average over θ ∈ G are invariant under replacing a representative x by −x, so the statement does not depend on the choice
--   - encoding: c/√(Nd³), m ≤ cN/d², y_1, …, y_m → c / √(N·d³); m : ℕ with (m : ℝ) ≤ c·N/d²; y : Fin m → ℝ^d; reason: the denominator is √(N d³), as the proof's bound |a_{2j+2}| ≥ c/(d2^ν√(ν+1)) ≥ c/√(Nd³) confirms
-- source:
--   Prabhu, Schwiegelshohn, Shyam, The Price of Capacities for Clustering Coresets, STOC 2027 submission (manuscript sha256 ec35f5ef…), p. 36, Lemma 10.6, eq. (25)

import Mathlib
import Definitions.Def_PriceCapacities_LowerBound_Fourier
import Definitions.Def_PriceCapacities_LowerBound_Pattern

namespace PriceCapacities.LowerBound

theorem lemma_10_6 :
    ∃ c : ℝ, 0 < c ∧ ∃ d0 : ℕ, ∀ d : ℕ, Even d → d0 ≤ d →
      ∃ ω : PatternIdx d → ℝ, (∀ x, 1 < ω x ∧ ω x < 2) ∧
        ∀ m : ℕ, (m : ℝ) ≤ c * (patternCount d : ℝ) / (d : ℝ) ^ 2 →
          ∀ y : Fin m → EuclideanSpace ℝ (Fin d),
            c / Real.sqrt ((patternCount d : ℝ) * (d : ℝ) ^ 3)
              ≤ (1 / (patternCount d : ℝ)) * ∑ θ : PatternIdx d,
                  |Phi ω (patternVec θ.1) - ∑ r, abs (inner ℝ (patternVec θ.1) (y r))| := by sorry

end PriceCapacities.LowerBound
