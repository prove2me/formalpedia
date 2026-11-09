-- Prove2me | Theorems.Thm_SpatialHalfspace_FullLabels_theorem_1_1
-- name    : SpatialHalfspace.FullLabels.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:28:45.56718+00:00
-- url     : https://prove2.me/theorems/e8e6fc19-298f-4bb0-8f92-75ddf5d4964c
-- title:
--   Theorem 1.1 — Proper and improper learning on the paired midpoint family
-- statement:
--   With the paper's construction — $\varepsilon_*=\alpha/8=1/512$, the marginal tuple $\mu_D$ on $n=2\lfloor D/2\rfloor$ terminals and the family $\mathcal M_D\subseteq\mathcal E(\mu_D)$, both independent of $p$ — the following hold. $\varepsilon_*>0$ and $\mathcal M_D\subseteq\mathcal E(\mu_D)$ for every $D\ge 2$. For each integer $p\ge 1$ there are an integer $D_0(p)\ge 2$ and constants $c,C>0$ such that for all $D\ge D_0(p)$, uniformly for $0<\varepsilon\le\varepsilon_*$ and $0<\delta\le 1/3$,
--
--   $$c\,D^{1+1/p}\ \le\ \mathrm{OptBM}^{\mathrm{prop}}_p(H_D,\mathcal M_D,\varepsilon,\delta)\ \le\ C\,D^{1+1/p},\tag{2}$$
--
--   and the proper lower bound also holds with exact local conditional label probabilities as inputs. In the improper case, for every $D\ge 2$ and $\varepsilon,\delta\in(0,1)$,
--
--   $$\mathrm{OptBM}^{\mathrm{imp}}_p(H_D,\mathcal M_D,\varepsilon,\delta)=0 .$$
--
--   This is the proper–improper separation: on $\mathcal M_D$, requiring a halfspace output costs $\Theta(D^{1+1/p})$ bit-meters while an improper learner needs no communication.
--
--   **Formalization Note** $\Theta(D^{1+1/p})$ is written with explicit constants $c,C$ and threshold $D_0$ chosen after $p$ and before $D,\varepsilon,\delta$. The source's explicit witnesses: lower bound $(a_0/24)\,q^{1+1/p}$ for $q=\lfloor D/2\rfloor\ge\max\{2^p,6/a_0\}$ (Theorem 4.3), hence $c=a_0/(24\cdot 3^{1+1/p})$ via $q\ge D/3$; the upper bound uses the grid placement of Theorem 5.1 with one report bit per nonroot terminal and $N=\lceil(2/\rho)\ln(n/\delta)\rceil$ samples (Appendix E), at cost at most $\sqrt p\,n\lceil n^{1/p}\rceil$, independent of $\varepsilon$ and $\delta$.
--
--   Differences from the source:
--
--   - generalization: there is an absolute constant ε_* > 0 and, for every D ≥ 2, a marginal tuple μ_D and a family M_D ⊆ E(μ_D), independent of p → the paper’s own witnesses ε_* = α/8 = 1/512 (App. E), μ_D of (17) and M_D of Definition 3.2, together with the clauses ε_* > 0 and M_D ⊆ E(μ_D); reason: stating the claim for the paper’s witnesses implies the existential statement; Theorem 1.2 refers to exactly these objects
--   - encoding: Θ(D^{1+1/p}) uniformly for 0 < ε ≤ ε_* and 0 < δ ≤ 1/3, for D ≥ D₀(p) → ∃ D₀ ≥ 2, ∃ c, C > 0 (after p) with both bounds for all D ≥ D₀, ε ∈ (0, ε_*], δ ∈ (0, 1/3]; reason: the meaning of Θ with constants independent of D, ε and δ
--   - encoding: an informal binary interactive protocol with shared and private tapes → the round model of the Protocol definition: one bit or nothing per direction per edge per round, local latched halting, a finite timed receive history at halting, local finalization that may discard unused receive or timing information, root output from its own input, tapes and final local state, prefix-freeness and cut replay, and almost-sure finite halting at every vertex; reason: finite local halting implements the source’s termination requirement; arbitrary delays and computation are uncharged, messages can be serialized into rounds, and cut replay of final states excludes uncharged timing or control information from affecting the output while allowing unused information to be discarded
--   - encoding: learners with expectations and success probabilities → learners with measurable transcripts and a root classifier jointly measurable in inputs, tapes and feature vector; reason: standing measurability convention; without it probabilities and expectations would be undefined
--   - encoding: real-valued costs → costs in [0, ∞] (ℝ≥0∞), nonterminating traffic has infinite length; reason: an infinite or empty infimum must not become 0
--   - encoding: sample-based learners with local access to i.i.d. examples → each local send, halt, finalization, and root-output operation depends on a finite sample prefix, with no uniform bound unless UsesSamples is stated; reason: finite execution can request only finitely many samples; the prefix may depend on the input, tapes and local history, so adaptive sample-based learners are included
-- source:
--   Yang, Spatial Communication Complexity of Agnostic Halfspace Learning, STOC 2027 submission #119 (2026), preprint, SHA-256 e5822ae144143c29214b0dab09b1a1863f55740d17b6f50ed091ddf8ffcaa692, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/119.pdf, printed p. 1, PDF p. 2, Theorem 1.1, eq. (2), printed pp. 1–2 (PDF pp. 2–3); ε_* = α/8 fixed in App. E, PDF p. 22

import Definitions.Def_SpatialHalfspace_FullLabels_Construction

open MeasureTheory ProbabilityTheory UnderstandingML
open scoped ENNReal InnerProductSpace

namespace SpatialHalfspace.FullLabels

/-- Theorem 1.1 (Proper and improper learning on the paired midpoint family), printed
pp. 1–2, with the source's own witnesses `ε_* = α/8 = 1/512` (App. E), `μ_D` and `M_D` (§3.2,
independent of `p`). `ε_* > 0` and `M_D ⊆ E(μ_D)`; for each `p ≥ 1` there are `D₀(p) ≥ 2` and
constants `c, C > 0` such that for all `D ≥ D₀(p)`, uniformly in `0 < ε ≤ ε_*` and `0 < δ ≤ 1/3`,
(2) `c D^{1+1/p} ≤ OptBM_p^prop(H_D, M_D, ε, δ) ≤ C D^{1+1/p}`, and the proper lower bound also
holds in the exact-kernel model. In the improper case, for every `D ≥ 2` and `ε, δ ∈ (0,1)`,
`OptBM_p^imp(H_D, M_D, ε, δ) = 0`. -/
theorem theorem_1_1 :
    0 < epsStar ∧ (∀ D : ℕ, 2 ≤ D → familyM D ⊆ env (muD D)) ∧
    (∀ p : ℕ, 1 ≤ p → ∃ D₀ : ℕ, 2 ≤ D₀ ∧ ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ D : ℕ, D₀ ≤ D → ∀ ε δ : ℝ, 0 < ε → ε ≤ epsStar → 0 < δ → δ ≤ 1 / 3 →
        ENNReal.ofReal (c * (D : ℝ) ^ (1 + 1 / (p : ℝ))) ≤
            OptBM p (SampleInp D) sampleModel true (familyM D) ε δ ∧
          OptBM p (SampleInp D) sampleModel true (familyM D) ε δ ≤
            ENNReal.ofReal (C * (D : ℝ) ^ (1 + 1 / (p : ℝ))) ∧
          ENNReal.ofReal (c * (D : ℝ) ^ (1 + 1 / (p : ℝ))) ≤
            OptBM p (KernelInp D) kernelModel true (familyM D) ε δ) ∧
    ∀ p : ℕ, 1 ≤ p → ∀ D : ℕ, 2 ≤ D → ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      OptBM p (SampleInp D) sampleModel false (familyM D) ε δ = 0 := by sorry

end SpatialHalfspace.FullLabels
