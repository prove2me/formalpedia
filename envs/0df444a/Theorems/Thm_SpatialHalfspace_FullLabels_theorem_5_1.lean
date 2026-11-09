-- Prove2me | Theorems.Thm_SpatialHalfspace_FullLabels_theorem_5_1
-- name    : SpatialHalfspace.FullLabels.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:32:18.684778+00:00
-- url     : https://prove2.me/theorems/5a571239-6714-4f92-b3ed-39988244416b
-- title:
--   Theorem 5.1 — Proper-learning upper bound
-- statement:
--   For every integer $p\ge 1$ there is a constant $C_p>0$ such that for every integer $D\ge 2$, $\varepsilon\in(0,1/4)$ and $\delta\in(0,1)$ there exist a $p$-dimensional substrate $G$ and a legal protocol $\Pi$ for a proper learner such that, for every $P\in\mathcal E(\mu_D)$,
--
--   $$\Pr\big[R_{\bar P}(\hat h)\le R^*_{\bar P}(H_D)+\varepsilon\big]\ \ge\ 1-\delta$$
--
--   and
--
--   $$\mathrm{BM}_G(\Pi;P)\ \le\ C_p\,D^{1+1/p}\big(1+\log(1/\varepsilon)\big).\tag{25}$$
--
--   In particular, the learner uses $O(\log(D/\delta)/\varepsilon^2)$ samples per terminal: at most $\lfloor C_{\mathrm{samp}}\log(D/\delta)/\varepsilon^2\rfloor$ for an absolute constant $C_{\mathrm{samp}}$.
--
--   **Formalization Note** The source's construction (App. B.4) places the terminals at distinct points of $\{0,\dots,g-1\}^p$, $g=\lceil n^{1/p}\rceil$, with the root at a terminal and straight links (total length $\le\sqrt p\,n g$), takes $\tau=\min\{1/8,\varepsilon/[4(\alpha+2\rho)]\}$, $K=3n$, $m_*=\alpha$ in Lemma B.3, and sends three fixed-length reports of $\lceil\log_2(\lceil 2/\tau\rceil+1)\rceil$ bits per nonroot terminal. Logarithms are natural (a change of base only changes constants).
--
--   Differences from the source:
--
--   - reading: O(log(D/δ)/ε²) samples per terminal → at most ⌊C_samp log(D/δ)/ε²⌋ samples per terminal with C_samp chosen before p, D, ε, δ; reason: the source’s N = ⌈8(M+L₀)/α⌉ depends only on n, δ and τ, so its O-constant is absolute
--   - encoding: the learner uses N samples per terminal → UsesSamples: every transmitted symbol and the root’s classifier depend on each terminal’s sequence only through its first N examples; reason: terminals hold infinite i.i.d. sequences in the sample model
--   - encoding: an informal binary interactive protocol with shared and private tapes → the round model of the Protocol definition: one bit or nothing per direction per edge per round, local latched halting, a finite timed receive history at halting, local finalization that may discard unused receive or timing information, root output from its own input, tapes and final local state, prefix-freeness and cut replay, and almost-sure finite halting at every vertex; reason: finite local halting implements the source’s termination requirement; arbitrary delays and computation are uncharged, messages can be serialized into rounds, and cut replay of final states excludes uncharged timing or control information from affecting the output while allowing unused information to be discarded
--   - encoding: learners with expectations and success probabilities → learners with measurable transcripts and a root classifier jointly measurable in inputs, tapes and feature vector; reason: standing measurability convention; without it probabilities and expectations would be undefined
--   - encoding: real-valued costs → costs in [0, ∞] (ℝ≥0∞), nonterminating traffic has infinite length; reason: an infinite or empty infimum must not become 0
--   - encoding: sample-based learners with local access to i.i.d. examples → each local send, halt, finalization, and root-output operation depends on a finite sample prefix, with no uniform bound unless UsesSamples is stated; reason: finite execution can request only finitely many samples; the prefix may depend on the input, tapes and local history, so adaptive sample-based learners are included
-- source:
--   Yang, Spatial Communication Complexity of Agnostic Halfspace Learning, STOC 2027 submission #119 (2026), preprint, SHA-256 e5822ae144143c29214b0dab09b1a1863f55740d17b6f50ed091ddf8ffcaa692, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/119.pdf, printed p. 11, PDF p. 12, Theorem 5.1, eq. (25), PDF p. 12 (proof in App. B.4, PDF p. 18)

import Definitions.Def_SpatialHalfspace_FullLabels_Construction

open MeasureTheory ProbabilityTheory UnderstandingML
open scoped ENNReal InnerProductSpace

namespace SpatialHalfspace.FullLabels

/-- Theorem 5.1 (Proper-learning upper bound), printed p. 11. For every `p ≥ 1` there is
`C_p > 0` such that for every `D ≥ 2`, `ε ∈ (0, 1/4)` and `δ ∈ (0,1)` there are a `p`-dimensional
substrate and a legal proper learner with `Pr[R_P(ĥ) ≤ R*_P(H_D) + ε] ≥ 1 − δ` and (25)
`BM_G(Π; P) ≤ C_p D^{1+1/p}(1 + log(1/ε))` for every `P ∈ E(μ_D)`; the learner uses
`O(log(D/δ)/ε²)` samples per terminal (here: at most `⌊C_samp log(D/δ)/ε²⌋` with an absolute
constant `C_samp`). -/
theorem theorem_5_1 : ∃ Csamp : ℝ, 0 < Csamp ∧ ∀ p : ℕ, 1 ≤ p → ∃ Cp : ℝ, 0 < Cp ∧
    ∀ D : ℕ, 2 ≤ D → ∀ ε δ : ℝ, 0 < ε → ε < 1 / 4 → 0 < δ → δ < 1 →
      ∃ (S : Substrate p (Term D)) (Pr : Protocol S (SampleInp D) (Vec D → Bool)),
        Pr.IsLearner true ∧ Pr.Achieves sampleModel (env (muD D)) ε (1 - δ) ∧
        (∀ Pt ∈ env (muD D), Pr.BM (sampleModel Pt) ≤
          ENNReal.ofReal (Cp * (D : ℝ) ^ (1 + 1 / (p : ℝ)) * (1 + Real.log (1 / ε)))) ∧
        Pr.UsesSamples ⌊Csamp * Real.log ((D : ℝ) / δ) / ε ^ 2⌋₊ := by sorry

end SpatialHalfspace.FullLabels
