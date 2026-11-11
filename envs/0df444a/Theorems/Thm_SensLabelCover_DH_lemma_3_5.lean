-- Prove2me | Theorems.Thm_SensLabelCover_DH_lemma_3_5
-- name    : SensLabelCover.DH.lemma_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:35:28.187458+00:00
-- url     : https://prove2.me/theorems/a7f16c15-fe98-488a-bee6-62010791fba2
-- title:
--   Lemma 3.5 — random-threshold selection changes its choice with probability at most $(1/w)\sum_{i\in A}|q_i-\tilde q_i|$
-- statement:
--   Let $J\subseteq[0,1]$ be an interval of length $w>0$ and let $q_1,\dots,q_R$ and $\tilde q_1,\dots,\tilde q_R$ be scores in $[0,1]$. Draw one threshold $\theta$ uniformly from $J$ and let $K$ and $\tilde K$ be the indices selected from the two lists (the smallest index whose score is at least $\theta$, or $0$ if none). With $A=\{i\in[R]:[\min\{q_i,\tilde q_i\},\max\{q_i,\tilde q_i\}]\cap J\neq\emptyset\}$,
--   $$\Pr[K\neq\tilde K]\le\frac1w\sum_{i\in A}|q_i-\tilde q_i|.$$
--   Moreover, for a finite alphabet $\Sigma$, an integer $N\ge1$ and candidates $z_0,z_1,\dots,z_R,\tilde z_1,\dots,\tilde z_R\in\Sigma^N$ with common default $\tilde z_0:=z_0$,
--   $$\mathbb E\,d_H(z_K,\tilde z_{\tilde K})\le\sum_{i=1}^R d_H(z_i,\tilde z_i)+\frac Nw\sum_{i\in A}|q_i-\tilde q_i|.$$
--
--   The lemma makes the selection rule a stable choice: small changes of the scores rarely change the selected candidate.
--
--   Differences from the source:
--   - encoding: indices $1,\dots,R$ and the default index $0$ → `Fin R` (0-based) and `none : Option (Fin R)`; $z_0$ → `z none`; reason: Lean convention, same instances.
--   - encoding: "an interval of length $w$" → an order-connected $J\subseteq[0,1]$ with Lebesgue measure $w$ (closed, open or half-open); reason: this is exactly an interval of length $w>0$.
--   - encoding: the probability and expectation over $\theta$ uniform on $J$ → $\mathrm{vol}(\cdot\cap J)/w$, and the expectation as $\sum_{(k,\tilde k)}\Pr[K=k,\tilde K=\tilde k]\,d_H(z_k,\tilde z_{\tilde k})$; reason: same quantities, no integrability side condition.
-- source:
--   Fleming, Hopkins, Yoshida, Sensitivity and Locality Lower Bounds via Low-Soundness Label Cover, STOC 2027 submission (manuscript sha256 5bfe95ad…), p. 21 (PDF 24), Lemma 3.5

import Mathlib
import Definitions.Def_SensLabelCover_DH_ThresholdSelection

open MeasureTheory

namespace SensLabelCover.DH

/-- Lemma 3.5 (Random-threshold selection), p. 21 (PDF p. 24). `J ⊆ [0, 1]` is an interval
(order-connected) of length `w > 0`; the threshold `θ` is uniform on `J`. -/
theorem lemma_3_5 (J : Set ℝ) (w : ℝ) (hw : 0 < w) (hJ : J.OrdConnected)
    (hJ01 : J ⊆ Set.Icc 0 1) (hJw : volume J = ENNReal.ofReal w) {R : ℕ} (q q' : Fin R → ℝ)
    (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1) (hq' : ∀ i, q' i ∈ Set.Icc (0 : ℝ) 1) :
    thresholdProb J w {θ | select q θ ≠ select q' θ} ≤
        (1 / w) * ∑ i ∈ crossingSet J q q', |q i - q' i| ∧
      ∀ (Alph : Type) [Fintype Alph] [DecidableEq Alph] (N : ℕ), 0 < N →
        ∀ z z' : Option (Fin R) → (Fin N → Alph), z' none = z none →
          ∑ kk : Option (Fin R) × Option (Fin R),
              thresholdProb J w {θ | select q θ = kk.1 ∧ select q' θ = kk.2} *
                (hammingDist (z kk.1) (z' kk.2) : ℝ) ≤
            ∑ i : Fin R, (hammingDist (z (some i)) (z' (some i)) : ℝ) +
              ((N : ℝ) / w) * ∑ i ∈ crossingSet J q q', |q i - q' i| := by sorry

end SensLabelCover.DH
