-- Prove2me | Theorems.Thm_SpatialHalfspace_FullLabels_theorem_1_2
-- name    : SpatialHalfspace.FullLabels.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:29:48.455434+00:00
-- url     : https://prove2.me/theorems/7771db5f-1e55-45b2-b301-7fe93d8616e2
-- title:
--   Theorem 1.2 — Arbitrary conditional labels: optimal bit-meter cost $\Theta(D^{1+1/p})$
-- statement:
--   Let $\mu_D$ be the marginal tuples of §3.2 and $\varepsilon_*=1/512$. For every fixed integer $p\ge 1$ and fixed $\varepsilon\in(0,\varepsilon_*]$ there are constants $c,C>0$ and an integer $D_0\ge 2$ such that for all $D\ge D_0$ and uniformly for $0<\delta\le 1/3$,
--
--   $$c\,D^{1+1/p}\le \mathrm{OptBM}^{\mathrm{prop}}_p(H_D,\mathcal E(\mu_D),\varepsilon,\delta)\le C\,D^{1+1/p},\tag{3}$$
--
--   $$c\,D^{1+1/p}\le \mathrm{OptBM}^{\mathrm{imp}}_p(H_D,\mathcal E(\mu_D),\varepsilon,\delta)\le C\,D^{1+1/p}.\tag{4}$$
--
--   Both lower bounds remain valid when each terminal is given its exact conditional label probabilities. A proper learner achieves the upper bound using $O(\log(D/\delta)/\varepsilon^2)$ samples per terminal: there are a substrate and a proper learner that succeed for every $P\in\mathcal E(\mu_D)$, have worst-case cost at most $C D^{1+1/p}$, and use at most $\lfloor C_{\mathrm{samp}}\log(D/\delta)/\varepsilon^2\rfloor$ samples per terminal, with an absolute constant $C_{\mathrm{samp}}$.
--
--   In physical dimensions $2$ and $3$ the optimal costs are $\Theta(D^{3/2})$ and $\Theta(D^{4/3})$.
--
--   **Formalization Note** $\Theta$ is written with explicit constants: $c$, $C$, $D_0$ are chosen after $p$ and $\varepsilon$ and before $D$ and $\delta$; $C_{\mathrm{samp}}$ is chosen first. The source's explicit witnesses are: proper lower constant $(a_0/24)q^{1+1/p}$ for $q\ge\max\{2^p,6/a_0\}$ (Theorem 4.3), improper lower constant $a_0 q^{1+1/p}/(24\cdot 2^{1/p})$ for $q\ge\max\{2^{p+1},6/a_0\}$ (Lemma D.2 with $m=q$), $q=\lfloor D/2\rfloor\ge D/3$; the upper bound is Theorem 5.1's grid protocol with $\tau=\min\{1/8,\varepsilon/[4(\alpha+2\rho)]\}$, $K=3n$, $m_*=\alpha$, $L_0=\ln(4K/\delta)$, $M=\lceil 2L_0/\tau^2\rceil$, $N=\lceil 8(M+L_0)/\alpha\rceil$ samples and three $\lceil\log_2(\lceil 2/\tau\rceil+1)\rceil$-bit reports per nonroot terminal, so cost at most $3L\sqrt p\,n\lceil n^{1/p}\rceil$.
--
--   Differences from the source:
--
--   - reading: the marginal tuples μ_D and constant ε_* above → μ_D of (17) and ε_* = α/8 = 1/512; reason: Appendix E fixes ε_* = α/8 in the proof of Theorem 1.1, to which Theorem 1.2 refers
--   - generalization: the lower bounds of (3)–(4) for the sample model → the same lower bounds also in the exact-kernel model; reason: the abstract and §6 state this, and App. D.2 and Theorem 4.3 prove the lower bounds in the exact-kernel model; it implies the sample-model statement by Lemma 2.5
--   - encoding: Θ(D^{1+1/p}) for all sufficiently large D, uniformly for 0 < δ ≤ 1/3 → ∃ c, C > 0 and D₀ ≥ 2 (after p, ε) with both bounds for all D ≥ D₀ and δ ∈ (0, 1/3]; reason: the meaning of Θ with constants independent of D and δ
--   - reading: a proper learner achieves the upper bound using O(log(D/δ)/ε²) samples per terminal → ∃ substrate and proper learner achieving (ε, 1 − δ) on E(μ_D) with worst-case cost ≤ C D^{1+1/p} and at most ⌊C_samp log(D/δ)/ε²⌋ samples per terminal, C_samp absolute; reason: the source’s sample count N depends only on n, δ and τ, so the O-constant is absolute
--   - encoding: an informal binary interactive protocol with shared and private tapes → the round model of the Protocol definition: one bit or nothing per direction per edge per round, local latched halting, a finite timed receive history at halting, local finalization that may discard unused receive or timing information, root output from its own input, tapes and final local state, prefix-freeness and cut replay, and almost-sure finite halting at every vertex; reason: finite local halting implements the source’s termination requirement; arbitrary delays and computation are uncharged, messages can be serialized into rounds, and cut replay of final states excludes uncharged timing or control information from affecting the output while allowing unused information to be discarded
--   - encoding: learners with expectations and success probabilities → learners with measurable transcripts and a root classifier jointly measurable in inputs, tapes and feature vector; reason: standing measurability convention; without it probabilities and expectations would be undefined
--   - encoding: real-valued costs → costs in [0, ∞] (ℝ≥0∞), nonterminating traffic has infinite length; reason: an infinite or empty infimum must not become 0
--   - encoding: sample-based learners with local access to i.i.d. examples → each local send, halt, finalization, and root-output operation depends on a finite sample prefix, with no uniform bound unless UsesSamples is stated; reason: finite execution can request only finitely many samples; the prefix may depend on the input, tapes and local history, so adaptive sample-based learners are included
-- source:
--   Yang, Spatial Communication Complexity of Agnostic Halfspace Learning, STOC 2027 submission #119 (2026), preprint, SHA-256 e5822ae144143c29214b0dab09b1a1863f55740d17b6f50ed091ddf8ffcaa692, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/119.pdf, printed p. 2, PDF p. 3, Theorem 1.2, eqs. (3)–(4), PDF p. 3; proof in App. E, PDF p. 22; exact-kernel validity of the lower bounds: abstract (PDF p. 1), §6 (PDF p. 13), App. D.2 (PDF p. 21)

import Definitions.Def_SpatialHalfspace_FullLabels_Construction

open MeasureTheory ProbabilityTheory UnderstandingML
open scoped ENNReal InnerProductSpace

namespace SpatialHalfspace.FullLabels

/-- Theorem 1.2 (Arbitrary conditional labels), printed p. 2 — the goal. For the marginal
tuples `μ_D` and `ε_* = 1/512`, every fixed `p ≥ 1` and fixed `ε ∈ (0, ε_*]`: there are constants
`c, C > 0` and `D₀` (independent of `D` and `δ`) such that for all `D ≥ D₀` and all `0 < δ ≤ 1/3`,
(3) `OptBM_p^prop(H_D, E(μ_D), ε, δ) = Θ(D^{1+1/p})` and (4) `OptBM_p^imp(H_D, E(μ_D), ε, δ) =
Θ(D^{1+1/p})`, both lower bounds also holding in the exact-kernel model; and a proper learner
achieves the upper bound using at most `⌊C_samp log(D/δ)/ε²⌋` samples per terminal, with an
absolute constant `C_samp`. -/
theorem theorem_1_2 : ∃ Csamp : ℝ, 0 < Csamp ∧
    ∀ p : ℕ, 1 ≤ p → ∀ ε : ℝ, 0 < ε → ε ≤ epsStar →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ D₀ : ℕ, 2 ≤ D₀ ∧
        ∀ D : ℕ, D₀ ≤ D → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 3 →
          ENNReal.ofReal (c * (D : ℝ) ^ (1 + 1 / (p : ℝ))) ≤
              OptBM p (SampleInp D) sampleModel true (env (muD D)) ε δ ∧
            OptBM p (SampleInp D) sampleModel true (env (muD D)) ε δ ≤
              ENNReal.ofReal (C * (D : ℝ) ^ (1 + 1 / (p : ℝ))) ∧
            ENNReal.ofReal (c * (D : ℝ) ^ (1 + 1 / (p : ℝ))) ≤
              OptBM p (SampleInp D) sampleModel false (env (muD D)) ε δ ∧
            OptBM p (SampleInp D) sampleModel false (env (muD D)) ε δ ≤
              ENNReal.ofReal (C * (D : ℝ) ^ (1 + 1 / (p : ℝ))) ∧
            ENNReal.ofReal (c * (D : ℝ) ^ (1 + 1 / (p : ℝ))) ≤
              OptBM p (KernelInp D) kernelModel true (env (muD D)) ε δ ∧
            ENNReal.ofReal (c * (D : ℝ) ^ (1 + 1 / (p : ℝ))) ≤
              OptBM p (KernelInp D) kernelModel false (env (muD D)) ε δ ∧
            ∃ (S : Substrate p (Term D)) (Pr : Protocol S (SampleInp D) (Vec D → Bool)),
              Pr.IsLearner true ∧ Pr.Achieves sampleModel (env (muD D)) ε (1 - δ) ∧
              Pr.worstBM sampleModel (env (muD D)) ≤
                ENNReal.ofReal (C * (D : ℝ) ^ (1 + 1 / (p : ℝ))) ∧
              Pr.UsesSamples ⌊Csamp * Real.log ((D : ℝ) / δ) / ε ^ 2⌋₊ := by sorry

end SpatialHalfspace.FullLabels
