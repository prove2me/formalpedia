-- Prove2me | Theorems.Thm_ParallelDiffusionLB_NearIsotropic_Supplement_theorem_4_1
-- name    : ParallelDiffusionLB.NearIsotropic.Supplement.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:10:53.43512+00:00
-- url     : https://prove2.me/theorems/d3600011-6980-4f8d-b6e1-ea3d1cacbf2e
-- title:
--   Theorem 4.1 — Linear parallel lower bound for anisotropic boxes
-- statement:
--   Let $a,b\in\mathbb N$. For all sufficiently large $d$, every query budget $1\le P\le d^a$ and every score accuracy $\varepsilon\ge d^{-b}$, there are finitely many instances $i$ with a probability law $\mu$ on them, and for each instance an axis-aligned box
--   $$K_i=\prod_{j=1}^d[l_{i,j},u_{i,j}],\qquad l_{i,j}<u_{i,j},$$
--   which is full-dimensional and contained in the open unit ball $B_2(0,1)$, together with a fixed legal score oracle $\hat s_i$ for $\pi_i=\mathrm{Unif}(K_i)$ at accuracy $\varepsilon$ (a jointly measurable map of $(x,\sigma)$ with $\mathbb E_{X\sim\pi_i^{(\sigma)}}\|\hat s_i(X,\sigma)-s_{\pi_i,\sigma}(X)\|_2^2\le\varepsilon^2/\sigma^2$ for every $\sigma>0$), such that the following holds. For every number of rounds $R<d$ and every randomized adaptive parallel algorithm with $R$ rounds of at most $P$ queries each and a seed of arbitrary law $\nu$, whose output law against instance $i$ is $Q_i$,
--   $$\mu\bigl(\{\,i:\ d_{TV}(Q_i,\pi_i)\ge0.9\,\}\bigr)\ge0.9.$$
--
--   The instance law, the boxes and the oracles are chosen before the algorithm. Compared with the goal (Theorem 3.1), the round lower bound here is linear in $d$, but the targets are strongly anisotropic rather than near-isotropic.
--
--   Differences from the source:
--   - encoding: for sufficiently large d, with a polynomial budget P = poly(d) and an inverse-polynomial accuracy ε_score = poly(d)^{-1} fixed beforehand → ∀ a b : ℕ, ∃ d₀, ∀ d ≥ d₀, ∀ P with 1 ≤ P ≤ d^a, ∀ ε > 0 with d^{-b} ≤ ε; reason: every polynomial budget is eventually at most d^a and every inverse polynomial eventually at least d^{-b}, for some a, b; this is the shape of the published theorem_3_1
--   - encoding: coordinates i ∈ [d] and labels k ∈ [M], 1-indexed → i : Fin d and k : Fin M, 0-indexed (paper i = i.val + 1, paper k = k.val + 1); reason: Lean convention; same objects
--   - encoding: a distribution over boxes K^θ → a probability measure μ on Fin K indexing finitely many boxes; reason: the paper's distribution (θ uniform on [M]^d) is finitely supported; an existential over finitely supported laws specializes to it
--   - encoding: full-dimensional axis-aligned boxes K^θ ⊂ B_2(0,1) → K_i = {x | ∀ j, l_i j ≤ x_j ≤ u_i j} with l_i j < u_i j for all j, and K_i ⊆ Metric.ball 0 1; reason: closed axis-aligned boxes with positive side lengths; the open ball is the stronger reading of B_2(0,1)
--   - encoding: π^θ = Unif(K^θ) → unifSet K_i = vol(K_i)⁻¹ • vol|_{K_i}; reason: the paper's uniform law of a set of positive finite volume
--   - encoding: every randomized sampler using fewer than d rounds → ∀ R < d, every probability law ν on an arbitrary seed space Ω and every ParallelAlgorithm with exactly P slots per round; reason: at most P queries are encoded by repeating queries; the published model of §2.2
--   - encoding: a fixed legal approximate oracle satisfying (1); Pr_θ[d_TV(Q^θ,π^θ) ≥ 0.9] ≥ 0.9 → LegalOracle (unifSet K_i) ε (o i), and 9/10 ≤ μ.real {i | 9/10 ≤ PolySampIso.tvDist (A.outputLaw ν (o i)) (unifSet K_i)}; reason: the published legality predicate, output law and total variation, as in theorem_3_1
-- source:
--   Yimeng Wang, Yiwen Kou, Lower Bounds for Parallel Diffusion Sampling, STOC 2027 submission #660 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/660.pdf, Theorem 4.1, p. 14 (proof p. 16; parameters (53)–(54), p. 30)

import Definitions.Def_ParallelDiffusionLB_NearIsotropic_Supplement_Box
import Definitions.Def_ParallelDiffusionLB_NearIsotropic_Algorithm
import Definitions.Def_PolySampIso_Divergences

open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

namespace ParallelDiffusionLB.NearIsotropic.Supplement

/-- Theorem 4.1 (Linear parallel lower bound), p. 14, with the polynomial budgets of §2.2 made
explicit, in the quantifier shape of the published `theorem_3_1`. The finite instance law, the
full-dimensional axis-aligned boxes `K_i = ∏_j [l_i j, u_i j] ⊂ B₂(0,1)` and their legal oracles
are chosen before quantifying over every round count `R < d` and every measurable randomized
algorithm with `P` query slots per round. -/
theorem theorem_4_1 (a b : ℕ) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ P : ℕ, 1 ≤ P → P ≤ d ^ a →
    ∀ ε : ℝ, 0 < ε → (d : ℝ) ^ (-(b : ℤ)) ≤ ε →
    ∃ K : ℕ, 0 < K ∧ ∃ μ : Measure (Fin K), IsProbabilityMeasure μ ∧
    ∃ l u : Fin K → Fin d → ℝ, ∃ o : Fin K → Query d → E d,
      (∀ i, (∀ j, l i j < u i j) ∧
        {x : E d | ∀ j, l i j ≤ x j ∧ x j ≤ u i j} ⊆ Metric.ball (0 : E d) 1 ∧
        LegalOracle (unifSet {x : E d | ∀ j, l i j ≤ x j ∧ x j ≤ u i j}) ε (o i)) ∧
      ∀ R : ℕ, R < d →
      ∀ (Ω : Type*) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
        (A : ParallelAlgorithm (Query d) (E d) (E d) Ω P R),
        (9 / 10 : ℝ) ≤ μ.real {i | (9 / 10 : ℝ) ≤
          PolySampIso.tvDist (A.outputLaw ν (o i))
            (unifSet {x : E d | ∀ j, l i j ≤ x j ∧ x j ≤ u i j})} := by sorry

end ParallelDiffusionLB.NearIsotropic.Supplement
