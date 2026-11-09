-- Prove2me | Theorems.Thm_SpatialHalfspace_FullLabels_lemma_4_2
-- name    : SpatialHalfspace.FullLabels.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:29:08.269487+00:00
-- url     : https://prove2.me/theorems/bbf62984-75b3-4ac5-8000-d7f452f4fb51
-- title:
--   Lemma 4.2 — Packing and radial integration
-- statement:
--   For $t\ge 0$, a ball of radius $t$ in $\mathbb R^p$ contains at most $(2t+1)^p$ points of a unit-separated set: if $A\subseteq\mathbb R^p$ has $\|x-y\|_2\ge 1$ for distinct $x,y\in A$, then for every centre $c$,
--
--   $$\big|A\cap \bar B(c,t)\big|\le (2t+1)^p .$$
--
--   Moreover, for every protocol $\Pi$ on a substrate $G$ (and every law of the inputs), with $d(v)=\|\varphi(v)-\varphi(r_\star)\|_2$, $W_t=\{v:d(v)\le t\}$ and $C_W=\sum_{f\in\partial_G W}\mathbb E|T_f|$,
--
--   $$\int_0^\infty C_{W_t}\,dt=\sum_{xy\in E_G}\mathbb E|T_{xy}|\;|d(x)-d(y)|\ \le\ \mathrm{BM}_G(\Pi).$$
--
--   This converts per-cut information bounds into a bit-meter lower bound.
--
--   Differences from the source:
--
--   - generalization: a radius-t ball → the closed ball of radius t around any centre; reason: the closed ball contains the open one, so the bound for closed balls implies the source’s
--   - generalization: for every protocol → every protocol on every substrate under every input measure, not necessarily a probability measure, legality not assumed; reason: the identity and the inequality are nonnegative accounting facts for arbitrary measures; the source’s probability-law case is included
--   - encoding: real-valued costs → costs in [0, ∞] (ℝ≥0∞), nonterminating traffic has infinite length; reason: an infinite or empty infimum must not become 0
--   - generalization: positive physical dimension p → all natural dimensions p, including p = 0; reason: in dimension zero a unit-separated set has at most one point and every root distance is zero; specializing to p ≥ 1 gives every source instance
-- source:
--   Yang, Spatial Communication Complexity of Agnostic Halfspace Learning, STOC 2027 submission #119 (2026), preprint, SHA-256 e5822ae144143c29214b0dab09b1a1863f55740d17b6f50ed091ddf8ffcaa692, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/119.pdf, printed p. 10, PDF p. 11, Lemma 4.2, PDF p. 11

import Definitions.Def_SpatialHalfspace_FullLabels_Construction

open MeasureTheory ProbabilityTheory UnderstandingML
open scoped ENNReal InnerProductSpace

namespace SpatialHalfspace.FullLabels

/-- Lemma 4.2 (Packing and radial integration), printed p. 10. For `t ≥ 0`, a (closed)
radius-`t` ball contains at most `(2t + 1)^p` points of a unit-separated set in `ℝ^p`. Moreover, for
every protocol (and every input law), with `d(v) = ‖φ(v) − φ(r⋆)‖₂` and `W_t = {v : d(v) ≤ t}`,
`∫_0^∞ C_{W_t} dt = ∑_{xy ∈ E_G} E|T_{xy}| |d(x) − d(y)| ≤ BM_G(Π)`. -/
theorem lemma_4_2 (p : ℕ) :
    (∀ A : Set (Phys p), (∀ x ∈ A, ∀ y ∈ A, x ≠ y → 1 ≤ dist x y) →
      ∀ (c : Phys p) (t : ℝ), 0 ≤ t →
        (A ∩ Metric.closedBall c t).Finite ∧
          ((A ∩ Metric.closedBall c t).ncard : ℝ) ≤ (2 * t + 1) ^ p) ∧
    ∀ {U : Type} [Fintype U] (S : Substrate p U) {Inp Out : Type} [MeasurableSpace Inp]
      (Pr : Protocol S Inp Out) (ν : Measure (U → Inp)),
      ∫⁻ t in Set.Ici (0 : ℝ), Pr.cutTraffic ν (S.ball t) =
          ∑ e, Pr.expLen ν e * ENNReal.ofReal |S.rootDist e.1.1 - S.rootDist e.1.2| ∧
        ∑ e, Pr.expLen ν e * ENNReal.ofReal |S.rootDist e.1.1 - S.rootDist e.1.2| ≤ Pr.BM ν := by sorry

end SpatialHalfspace.FullLabels
