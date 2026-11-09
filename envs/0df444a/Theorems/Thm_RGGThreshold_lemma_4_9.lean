-- Prove2me | Theorems.Thm_RGGThreshold_lemma_4_9
-- name    : RGGThreshold.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:59:44.002294+00:00
-- url     : https://prove2.me/theorems/09281e82-5a3d-4db5-b75d-f1d67e88cc5b
-- title:
--   Lemma 4.9 — conditional law of Gram–Schmidt coordinates
-- statement:
--   Let $x_1,\dots,x_n$ be independent uniform points of $\mathbb S^{d-1}$ and $v_i(j)$ their Gram–Schmidt coordinates. Let $1\le s<i\le n$ and $r_i(s)=\sqrt{1-\sum_{k=1}^{s-1}v_i(k)^2}$. Then:
--
--   1. conditional on $v_i(1),\dots,v_i(s-1)$, the value $v_i(s)/r_i(s)$ is distributed as the first coordinate of a uniform random point of $\mathbb S^{d-s}\subset\mathbb R^{d-s+1}$;
--   2. the first $i-1$ coordinates of $v_i$ have the same law as the first $i-1$ coordinates of a uniform random point of $\mathbb S^{d-1}$.
--
--   This is the Bartlett decomposition property on which the vertex-exposure argument rests.
--
--   **Formalization Note** The conditional law is the regular conditional distribution `condDistrib`, equal almost everywhere (for the law of the prefix) to the constant kernel. In 0-based labels the coordinate $c$ is the paper's $s-1$ and the vertex $i$ the paper's $i-1$.
--
--   Differences from the source:
--
--   - reading: "For a sequence of n linearly independent points" (standing assumption of §4.4) → hypothesis n ≤ d; reason: n points of the sphere are linearly independent with positive probability only if n ≤ d, and then almost surely
--   - encoding: "conditional on the coordinates, … is distributed as" → condDistrib equals the constant kernel almost everywhere for the law of the prefix; reason: Mathlib form of a conditional law
--   - encoding: vertices and coordinates 1, …, n → Fin n, numbered from 0; reason: index shift only; each statement shifts s accordingly
-- source:
--   Hunter–Milojević–Sudakov, Distinguishability Threshold for Random Geometric Graphs, arXiv:2607.22480 (held version, sha256 1a398ef9…), Lemma 4.9, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_RGGThreshold_gsCoord
import Definitions.Def_RGGThreshold_sphCDF
import Definitions.Def_RGGThreshold_setupStar

open MeasureTheory

namespace RGGThreshold

/-- **Lemma 4.9** (Hunter–Milojević–Sudakov, *Distinguishability Threshold for Random Geometric Graphs*, arXiv:2607.22480, held version, sha256 1a398ef9…, Lemma 4.9, p.14 (PDF p.16)). Let `x_1, …, x_n` be independent and
uniform on `S^{d-1}` and let `v_i(j)` be their Gram–Schmidt coordinates. For `1 ≤ s < i ≤ n`:
conditional on `v_i(1), …, v_i(s-1)`, the value `v_i(s)/r_i(s)` is distributed as the first
coordinate of a uniform point of `S^{d-s} ⊂ ℝ^{d-s+1}`, where `r_i(s) = √(1 - ∑_{k<s} v_i(k)²)`; in
other words, the first `i - 1` coordinates of `v_i` have the law of the first `i - 1` coordinates
of a uniform point of `S^{d-1}`.

**Formalization Note** 0-based: the coordinate `c` is the paper index `s - 1` and the vertex `i`
is the paper index `i - 1`, so `c < i`. The conditional law is `condDistrib`, equal almost
everywhere (for the law of the conditioning prefix) to the constant kernel. The hypothesis
`n ≤ d` is the standing assumption of §4.4 that `x_1, …, x_n` are linearly independent. -/
theorem lemma_4_9 (n d : ℕ) (hnd : n ≤ d) (c i : Fin n) (hci : c < i) :
    ProbabilityTheory.condDistrib
        (fun x : RGGDetect.Config n d => gsCoord x i c / residW c.val (gsCoord x) i)
        (fun x : RGGDetect.Config n d =>
          fun k : Fin c.val => gsCoord x i ⟨k.val, k.isLt.trans c.isLt⟩)
        (RGGDetect.prior n d)
      =ᵐ[(RGGDetect.prior n d).map (fun x : RGGDetect.Config n d =>
          fun k : Fin c.val => gsCoord x i ⟨k.val, k.isLt.trans c.isLt⟩)]
      ProbabilityTheory.Kernel.const _ ((RGGDetect.unifSphere (d - c.val)).map firstCoord) ∧
    (RGGDetect.prior n d).map (fun x : RGGDetect.Config n d =>
        fun k : Fin i.val => gsCoord x i ⟨k.val, k.isLt.trans i.isLt⟩) =
      (RGGDetect.unifSphere d).map (fun y : RGGDetect.Sph d =>
        fun k : Fin i.val => (y : EuclideanSpace ℝ (Fin d))
          ⟨k.val, lt_of_lt_of_le (k.isLt.trans i.isLt) hnd⟩) := by sorry

end RGGThreshold
