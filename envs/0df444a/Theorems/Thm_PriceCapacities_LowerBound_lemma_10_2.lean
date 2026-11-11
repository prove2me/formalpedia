-- Prove2me | Theorems.Thm_PriceCapacities_LowerBound_lemma_10_2
-- name    : PriceCapacities.LowerBound.lemma_10_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:24:48.882692+00:00
-- url     : https://prove2.me/theorems/45e37653-d4a4-4b27-9562-d6175fbba36a
-- title:
--   Lemma 10.2 — localization: disjoint $\eta$-neighborhoods, and coreset mass farther than $\eta$ from $P$ is $\tilde O_z(\varepsilon tn)$
-- statement:
--   Fix an integer $z\ge1$. There are constants $C_z,\kappa_\xi,\kappa_\eta,\kappa_N,\kappa_t>0$ and $d_0$, and $C>0$, $L\in\mathbb N$, all depending only on $z$, with the following property. Let $k\ge4$, $0<\varepsilon<1/4$ and $t\ge2$ with $\varepsilon t\Lambda^{z+20}\le\kappa_t$, where $\Lambda=\log(ek/\varepsilon)$. Then the parameters of §10.3 are well defined ($d\ge2$, $\eta=\kappa_\eta/(DMd^2)>0$), and for every choice of multiplicities $m_x=W_0\omega_x/(2N)$ (integer $W_0$, $1<\omega_x<2$), circle radius $0<\tau\le\eta/4$ with $\tau^2\le\varepsilon$, and circle phases for which the hard instance $P$ of §10.1 has $n=|P|\ge k/\varepsilon$ points:
--
--   1. the $\eta$-neighborhoods of the groups $P_{aij}$ are pairwise disjoint;
--   2. for every capacitated $\varepsilon$-coreset $Q$ for $P$ (with $k$ centers and exponent $z$) with fewer than $n$ support points, the restriction $Q_{\rm far}$ of $Q$ to the points $y$ with $\operatorname{dist}(y,P)>\eta$ satisfies
--   $$\mathbf 1(Q_{\rm far})\le C\,\varepsilon\,t\,n\,\Lambda^L ,$$
--   i.e. $\mathbf 1(Q_{\rm far})\le\tilde O_z(\varepsilon tn)$.
--
--   Almost all coreset weight therefore lies near the input; this is the first of the three lemmas behind Theorem 10.1.
--
--   Differences from the source:
--
--   - reading: 'for these parameter choices' with C_z sufficiently large and κ_ξ, κ_η, κ_N, κ_t sufficiently small constants depending only on z (§10.3) → ∃ C_z, κ_ξ, κ_η, κ_N, κ_t > 0 and d_0 ∈ ℕ, together with the Õ_z constant C > 0 and log degree L, all depending only on z and chosen before k, ε, t, such that the conclusion holds for every k ≥ 4, 0 < ε < 1/4, t ≥ 2 with εtH ≤ κ_t; reason: CAPTAIN_BRIEF rule 11; the constants of §10.3 are fixed once as functions of z; d_0 is the threshold of Lemma 10.6, which the source enlarges at will
--   - reading: the parameter choices of §10.3 exist → the conclusion also asserts d ≥ 2 and η > 0 for every admissible (k, ε, t); reason: the source chooses d (largest even d ≥ d_0 with 2^{d−1} < κ_N/(εtH)²), which presupposes that such d exists; stating it rules out constants for which the construction is undefined
--   - reading: D minimal with A = 2^D ≥ C_z(tD)^z; d even with N = 2^{d−1} the largest such value below κ_N/(εtH)² → D the least integer ≥ 1 with 2^D ≥ C_z(tD)^z; d the largest even integer ≥ max(2, d_0) with 2^{d−1} < κ_N/(εtH)²; reason: §10.1 requires A ≥ 2 (D = 0 always satisfies the inequality) and an even d ≥ 2
--   - generalization: weights ω_x supplied by Lemma 10.6, m_x = W_0ω_x/(2N), W_0 an integer with n ≥ k/ε → any multiplicities m_x = W_0ω_x/(2N) with W_0 ∈ ℕ and weights 1 < ω_x < 2, and |P| ≥ k/ε; reason: Lemma 10.6's weights satisfy 1 < ω_x < 2; the localization and measurement arguments use no other property of them
--   - reading: circle realization with 'a common sufficiently small radius' τ, τ ≤ η/4, τ² ≤ ε; m_x distinct equally spaced circle points → every 0 < τ ≤ η/4 with τ² ≤ ε and every phase φ of each circle; reason: the explicit conditions of p. 35; the source does not fix the phases, so every choice is covered
--   - encoding: copies a with u_a = ±1/√D vectors; mutually orthogonal copy, cluster, row, pattern, circle and n + 1 extra coordinates → copies indexed by Cube D (u_a = a/√D); the space EuclideanSpace ℝ (Fin D ⊕ Fin B ⊕ Fin q ⊕ Fin d ⊕ Fin 2 ⊕ Fin (n+1)) with n = 2AqBΣm_x; P = hardData.points, n = |P|; reason: a sum of coordinate blocks is a Euclidean space of the same dimension
--   - encoding: η-neighborhood; dist(y, P) > η → closed neighborhood {y : infDist y S ≤ η}; far part {y : η < infDist y P}; reason: Q_far is exactly the coreset mass not within distance η of an input point
--   - encoding: Õ_z(·) with Λ = log(ek/ε) → C·(·)·Λ^L with the constants above; reason: the convention of p. 32
-- source:
--   Prabhu, Schwiegelshohn, Shyam, The Price of Capacities for Clustering Coresets, STOC 2027 submission (manuscript sha256 ec35f5ef…), p. 33, Lemma 10.2 (parameters: pp. 34–35, §10.3)

import Mathlib
import Definitions.Def_PriceCapacities_LowerBound_WeightedSets
import Definitions.Def_PriceCapacities_LowerBound_CapacitatedCost
import Definitions.Def_PriceCapacities_LowerBound_CapacitatedCoreset
import Definitions.Def_PriceCapacities_LowerBound_Fourier
import Definitions.Def_PriceCapacities_LowerBound_Pattern
import Definitions.Def_PriceCapacities_LowerBound_HardInstance

namespace PriceCapacities.LowerBound

theorem lemma_10_2 (z : ℕ) (hz : 1 ≤ z) :
    ∃ c : HardConsts, 0 < c.Cz ∧ 0 < c.κξ ∧ 0 < c.κη ∧ 0 < c.κN ∧ 0 < c.κt ∧
    ∃ C : ℝ, 0 < C ∧ ∃ L : ℕ,
      ∀ k : ℕ, 4 ≤ k → ∀ ε : ℝ, 0 < ε → ε < 1 / 4 → ∀ t : ℝ, 2 ≤ t →
        ε * t * logScale k ε ^ (z + 20) ≤ c.κt →
        2 ≤ patternDim c z k ε t ∧ 0 < etaPar c z k ε t ∧
        ∀ m : PatternIdx (patternDim c z k ε t) → ℕ, IsPatternMultiplicity m →
        ∀ τ : ℝ, 0 < τ → τ ≤ etaPar c z k ε t / 4 → τ ^ 2 ≤ ε →
        ∀ φ : (Cube (copyDim c z t) × Fin (numRows k) × Fin (numCols k t)) →
            PatternIdx (patternDim c z k ε t) → Bool → ℝ,
          (k : ℝ) / ε ≤ ((hardData c z k ε t m τ φ).points.card : ℝ) →
          (∀ g g' : (hardData c z k ε t m τ φ).GroupIdx, g ≠ g' →
            Disjoint ((hardData c z k ε t m τ φ).nbhd (etaPar c z k ε t)
                ((hardData c z k ε t m τ φ).group g))
              ((hardData c z k ε t m τ φ).nbhd (etaPar c z k ε t)
                ((hardData c z k ε t m τ φ).group g'))) ∧
          ∀ Q : WeightedSet (hardData c z k ε t m τ φ).Space,
            IsCapacitatedCoreset k (z : ℝ) ε (unweighted (hardData c z k ε t m τ φ).points) Q →
            size Q < (hardData c z k ε t m τ φ).points.card →
            totalWeight ((hardData c z k ε t m τ φ).far Q (etaPar c z k ε t))
              ≤ C * ε * t * ((hardData c z k ε t m τ φ).points.card : ℝ) * logScale k ε ^ L := by sorry

end PriceCapacities.LowerBound
