-- Prove2me | Theorems.Thm_PriceCapacities_LowerBound_lemma_10_3
-- name    : PriceCapacities.LowerBound.lemma_10_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:24:17.984131+00:00
-- url     : https://prove2.me/theorems/b67bec32-c112-4869-b780-c73e3fd58f99
-- title:
--   Lemma 10.3 — measurement: in at least $9A/10$ copies every selected projection-error sum is $\tilde O_z(\varepsilon n/t^{z-1})$
-- statement:
--   Fix an integer $z\ge1$. There are constants $C_z,\kappa_\xi,\kappa_\eta,\kappa_N,\kappa_t>0$ and $d_0$, and $C>0$, $L\in\mathbb N$, all depending only on $z$, with the following property. Let $k\ge4$, $0<\varepsilon<1/4$ and $t\ge2$ with $\varepsilon t\Lambda^{z+20}\le\kappa_t$ ($\Lambda=\log(ek/\varepsilon)$). Then the parameters of §10.3 are well defined ($d\ge2$, $\eta>0$), and for every choice of multiplicities $m_x=W_0\omega_x/(2N)$ (integer $W_0$, $1<\omega_x<2$), circle radius $0<\tau\le\eta/4$ with $\tau^2\le\varepsilon$ and circle phases for which the hard instance $P$ has $n=|P|\ge k/\varepsilon$ points, and for every capacitated $\varepsilon$-coreset $Q$ for $P$ with fewer than $n$ support points (as in Lemma 10.2), at least $9A/10$ of the $A=2^D$ copies $a$ satisfy
--   $$\Big|\sum_{i=1}^q\sum_{j\in J_i}E_{aij}(\theta_i)\Big|\le C\,\frac{\varepsilon n}{t^{z-1}}\,\Lambda^L$$
--   simultaneously for all sets $J_i\subseteq[B]$ and all unit directions $\theta_i$ in the pattern coordinates. Here $E_{aij}(\theta)=\varphi_\theta(Q_{aij})-\varphi_\theta(P_{aij})$, $\varphi_\theta(y)=|\langle\theta,y\rangle|$, and $Q_{aij}$ is the restriction of $Q$ to the $\eta$-neighborhood of the group $P_{aij}$.
--
--   The coreset thus reproduces the projection sums of the selected groups in most copies; together with Lemma 10.6 this forces many coreset points per group.
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
--   - encoding: at least 9A/10 copies a satisfy … → ∃ a Finset `good` of copies with 9·2^D ≤ 10·|good| such that every a ∈ good satisfies the bound for all J, θ; reason: same count; the supremum over (J_i, θ_i) is inside, as printed
--   - encoding: J_i ⊆ [B], unit θ_i in the pattern coordinates, rows i = 1..q → J : Fin q → Finset (Fin B), θ : Fin q → ℝ^d with ‖θ i‖ = 1, embedded by patternEmbed; reason: same objects; 0-based
--   - reading: Q as in Lemma 10.2, 'these parameter choices' → Lemma 10.3 carries its own existential constants; reason: each lemma is stated with the §10.3 constants existentially quantified (CAPTAIN_BRIEF rule 11)
-- source:
--   Prabhu, Schwiegelshohn, Shyam, The Price of Capacities for Clustering Coresets, STOC 2027 submission (manuscript sha256 ec35f5ef…), p. 33, Lemma 10.3 (parameters: pp. 34–35, §10.3)

import Mathlib
import Definitions.Def_PriceCapacities_LowerBound_WeightedSets
import Definitions.Def_PriceCapacities_LowerBound_CapacitatedCost
import Definitions.Def_PriceCapacities_LowerBound_CapacitatedCoreset
import Definitions.Def_PriceCapacities_LowerBound_Fourier
import Definitions.Def_PriceCapacities_LowerBound_Pattern
import Definitions.Def_PriceCapacities_LowerBound_HardInstance

namespace PriceCapacities.LowerBound

theorem lemma_10_3 (z : ℕ) (hz : 1 ≤ z) :
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
          ∀ Q : WeightedSet (hardData c z k ε t m τ φ).Space,
            IsCapacitatedCoreset k (z : ℝ) ε (unweighted (hardData c z k ε t m τ φ).points) Q →
            size Q < (hardData c z k ε t m τ φ).points.card →
            ∃ good : Finset (Cube (copyDim c z t)),
              (9 : ℝ) * 2 ^ copyDim c z t ≤ 10 * (good.card : ℝ) ∧
              ∀ a ∈ good,
                ∀ (J : Fin (numRows k) → Finset (Fin (numCols k t)))
                  (θ : Fin (numRows k) → EuclideanSpace ℝ (Fin (patternDim c z k ε t))),
                  (∀ i, ‖θ i‖ = 1) →
                  |∑ i, ∑ j ∈ J i,
                      (hardData c z k ε t m τ φ).projErr Q (etaPar c z k ε t) (a, i, j) (θ i)|
                    ≤ C * ε * ((hardData c z k ε t m τ φ).points.card : ℝ) / t ^ (z - 1)
                        * logScale k ε ^ L := by sorry

end PriceCapacities.LowerBound
