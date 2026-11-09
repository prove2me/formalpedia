-- Prove2me | Theorems.Thm_SpatialHalfspace_FullLabels_theorem_4_3
-- name    : SpatialHalfspace.FullLabels.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:29:23.595483+00:00
-- url     : https://prove2.me/theorems/74b7b475-26e6-4ce1-aba5-ade87be19472
-- title:
--   Theorem 4.3 — Proper-learning lower bound
-- statement:
--   Let $a_0=1-h_2(1/4)>0$, $p\ge 1$, and $q=\lfloor D/2\rfloor\ge\max\{2^p,6/a_0\}$. For $0<\varepsilon\le\alpha/8$, every proper learner that uses a legal protocol $\Pi$ and achieves excess risk at most $\varepsilon$ with probability at least $2/3$ for every $P^\sigma\in\mathcal M_D$ satisfies, on every unit-separated $p$-dimensional substrate $G$,
--
--   $$\sup_\sigma \mathrm{BM}_G(\Pi;P^\sigma)\ \ge\ \frac{a_0}{24}\,q^{1+1/p}.\tag{24}$$
--
--   The same bound holds in the exact-kernel model.
--
--   This is the proper half of the lower bounds in Theorems 1.1 and 1.2.
--
--   Differences from the source:
--
--   - encoding: a proper learner using a legal protocol that achieves excess risk ≤ ε with probability ≥ 2/3 for every P^σ ∈ M_D → a protocol with IsLearner true (measurability, halfspace output on every execution) and Achieves on M_D with confidence 2/3 (legal and successful for every P^σ); reason: the learner notions of Definition 2.4
--   - encoding: an informal binary interactive protocol with shared and private tapes → the round model of the Protocol definition: one bit or nothing per direction per edge per round, local latched halting, a finite timed receive history at halting, local finalization that may discard unused receive or timing information, root output from its own input, tapes and final local state, prefix-freeness and cut replay, and almost-sure finite halting at every vertex; reason: finite local halting implements the source’s termination requirement; arbitrary delays and computation are uncharged, messages can be serialized into rounds, and cut replay of final states excludes uncharged timing or control information from affecting the output while allowing unused information to be discarded
--   - encoding: real-valued costs → costs in [0, ∞] (ℝ≥0∞), nonterminating traffic has infinite length; reason: an infinite or empty infimum must not become 0
--   - encoding: sample-based learners with local access to i.i.d. examples → each local send, halt, finalization, and root-output operation depends on a finite sample prefix, with no uniform bound unless UsesSamples is stated; reason: finite execution can request only finitely many samples; the prefix may depend on the input, tapes and local history, so adaptive sample-based learners are included
-- source:
--   Yang, Spatial Communication Complexity of Agnostic Halfspace Learning, STOC 2027 submission #119 (2026), preprint, SHA-256 e5822ae144143c29214b0dab09b1a1863f55740d17b6f50ed091ddf8ffcaa692, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/119.pdf, printed p. 10, PDF p. 11, Theorem 4.3, eq. (24), PDF p. 11 (proof PDF p. 12)

import Definitions.Def_SpatialHalfspace_FullLabels_Construction

open MeasureTheory ProbabilityTheory UnderstandingML
open scoped ENNReal InnerProductSpace

namespace SpatialHalfspace.FullLabels

/-- Theorem 4.3 (Proper-learning lower bound), printed p. 10. Let `a₀ = 1 − h₂(1/4)` and
`q ≥ max{2^p, 6/a₀}`. For `0 < ε ≤ α/8`, every proper learner using a legal protocol `Π` that
achieves excess risk at most `ε` with probability at least `2/3` for every `P^σ ∈ M_D` satisfies
(24) `sup_σ BM_G(Π; P^σ) ≥ (a₀/24) q^{1+1/p}` on every unit-separated `p`-dimensional substrate.
The same bound holds in the exact-kernel model. -/
theorem theorem_4_3 (p D : ℕ) (hp : 1 ≤ p) (hq1 : (2 : ℝ) ^ p ≤ ((D / 2 : ℕ) : ℝ))
    (hq2 : 6 / a0 ≤ ((D / 2 : ℕ) : ℝ)) (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ alpha / 8)
    (S : Substrate p (Term D)) :
    (∀ Pr : Protocol S (SampleInp D) (Vec D → Bool), Pr.IsLearner true →
      Pr.Achieves sampleModel (familyM D) ε (2 / 3) →
      ENNReal.ofReal (a0 / 24 * ((D / 2 : ℕ) : ℝ) ^ (1 + 1 / (p : ℝ))) ≤
        ⨆ σ : Term D → Bool, Pr.BM (sampleModel (PM D σ))) ∧
    ∀ Pr : Protocol S (KernelInp D) (Vec D → Bool), Pr.IsLearner true →
      Pr.Achieves kernelModel (familyM D) ε (2 / 3) →
      ENNReal.ofReal (a0 / 24 * ((D / 2 : ℕ) : ℝ) ^ (1 + 1 / (p : ℝ))) ≤
        ⨆ σ : Term D → Bool, Pr.BM (kernelModel (PM D σ)) := by sorry

end SpatialHalfspace.FullLabels
