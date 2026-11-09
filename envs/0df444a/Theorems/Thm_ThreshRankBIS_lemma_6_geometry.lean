-- Prove2me | Theorems.Thm_ThreshRankBIS_lemma_6_geometry
-- name    : ThreshRankBIS.lemma_6_geometry
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:07:25.448366+00:00
-- url     : https://prove2.me/theorems/0e51649e-5480-4f18-8db4-c991d59113a7
-- title:
--   Proof of Lemma 6 — sampling bodies $K_s$, the volume bound and coverage
-- statement:
--   Let $N,k\ge1$, let $W\in\mathbb R^{N\times k}$ have orthonormal columns, $U=\mathrm{range}(W)$, $P=[0,1]^N$, and for the scales $s=2^j$, $0\le j\le\lceil\log_2N\rceil$,
--
--   $$
--   K_s=\{a\in\mathbb R^k:\ \mathrm{dist}(Wa,P)^2\le s\}.
--   $$
--
--   1. *Sampling bodies.* Each $K_s$ is convex, contains the closed unit ball and lies in the open ball of radius $32(N+1)$.
--   2. *A volume bound for each target.* Fix $S\subseteq[N]$, $z=\mathbf 1_S$, and $a^*$ with $Wa^*=\Pi_Uz$. For every scale $s\ge\max\{1,\mathrm{dist}(z,U)^2\}$: $a^*\in K_s$; $L=(7a^*+K_s)/8\subseteq K_s$ and $\mathrm{vol}(L)=8^{-k}\mathrm{vol}(K_s)$; rounding $Wa$ at $1/2$ makes at most $64s/9$ errors for every $a\in L$; every probability measure within total variation $8^{-k}/4$ of the uniform law on $K_s$ gives $L$ mass at least $3\cdot8^{-k}/4$; and for $0<\beta<1$, $\lceil4\cdot8^k(N+\log(1/\beta)+1)\rceil$ independent samples from such a measure all miss $L$ with probability at most $2^{-N}\beta$.
--   3. The smallest scale $s\ge\max\{1,\mathrm{dist}(z,U)^2\}$ satisfies $s\le2\max\{1,\mathrm{dist}(z,U)^2\}$, and then every $a\in L$ rounds to a set $C$ with $|S\triangle C|\le16(\mathrm{dist}(z,U)^2+1)$.
--
--   These are the geometric facts behind the paper's list of $2^{O(k)}\mathrm{poly}(N)\log(2/\beta)$ approximate cuts: a constant-factor homothet of a sampling body rounds to a good approximation of a fixed target and occupies a $2^{-O(k)}$ fraction of its volume.
--
--   **Formalization Note** Rounding at $1/2$ selects the coordinates with $(Wa)_i\ge1/2$; total variation from the uniform law on $K_s$ is the supremum over measurable sets of the difference of masses; independent samples are the product measure.
--
--   Differences from the source:
--   - generalization: U the spectral subspace of L_G with a supplied orthonormal basis matrix W → W any linear isometry ℝ^k → ℝ^N (any k-dimensional subspace with an orthonormal basis), U = range W; reason: the proof uses only that the columns of W are orthonormal; the spectral subspace with its supplied basis is an instance
--   - generalization: the smallest scale s ≥ max{1, dist(z, U)²} → the membership, volume, rounding, sample-success and miss bounds for every scale 2^j ≥ max{1, dist(z, U)²}, j ≤ ⌈log₂ N⌉, plus the existence of a scale with s ≤ 2 max{1, dist(z, U)²} and the 16(dist² + 1) bound for it; reason: those bounds never use minimality; the smallest scale is one such scale and is the one with s ≤ 2 max{1, dist²}
--   - reading: hit-and-run samples within total variation 8^{−k}/4 of uniform; an approximate uniform sample succeeds with probability at least 3·8^{−k}/4; each fixed target is missed with probability at most 2^{−N}β → for every probability measure ν with |ν(B) − vol(B ∩ K_s)/vol(K_s)| ≤ 8^{−k}/4 for all measurable B: ν(L) ≥ 3·8^{−k}/4, and the product measure ν^{⊗m}, m = ⌈4·8^k(N + log(1/β) + 1)⌉, gives the event that no sample lies in L mass at most 2^{−N}β; reason: the claims concern any sampler with that accuracy; the hit-and-run mixing bound [10] is a cited black box and is not part of the statement
--   - reading: round each sampled Wa at 1/2; each body contains the unit ball and lies in a ball of radius 32(N + 1) → coordinate i is in the rounded set iff (Wa)_i ≥ 1/2; the closed unit ball ⊆ K_s ⊆ the open ball of radius 32(N + 1); reason: the margin to the threshold is 3/8, so either rounding convention gives the same error bound; the closed inner and open outer balls are the stronger choices and imply the other readings
-- source:
--   Carlson–Kolla, Efficient Algorithms for Approximately Counting Bipartite Independent Sets in Low Threshold Rank Graphs, STOC 2027 submission (manuscript sha256 9b315e04…), Proof of Lemma 6, The sampling bodies, A volume bound for each target, Simultaneous coverage, p.9

import Mathlib
import Definitions.Def_ThreshRankBIS_thresholdRank
set_option autoImplicit false
open Finset MeasureTheory

namespace ThreshRankBIS

/-- **Proof of Lemma 6: the sampling bodies, the volume bound for each target, and simultaneous
coverage**, p.9. Let `W : ℝ^k → ℝ^N` have orthonormal columns (`k ≥ 1`), `U = range W`,
`P = [0,1]^N`, and `K_s = {a ∈ ℝ^k : dist(Wa, P)² ≤ s}` for the scales `s = 2^j`,
`0 ≤ j ≤ ⌈log₂ N⌉`.
1. *Sampling bodies.* Each `K_s` is convex, contains the closed unit ball and lies in the
   (open) ball of radius `32(N + 1)`.
2. *Volume bound.* Fix `S ⊆ [N]`, `z = 1_S`, `u = Π_U z = W a*`. For every scale
   `s ≥ max{1, dist(z, U)²}`: `a* ∈ K_s`, `L = (7a* + K_s)/8 ⊆ K_s`, `vol(L) = 8^{−k} vol(K_s)`,
   rounding `Wa` at `1/2` makes at most `64s/9` errors for every `a ∈ L`, and every probability
   measure within total variation `8^{−k}/4` of the uniform law on `K_s` gives `L` mass at least
   `3·8^{−k}/4`. The smallest such scale satisfies `s ≤ 2max{1, dist(z, U)²}`, and then every
   `a ∈ L` rounds with at most `16(dist(z, U)² + 1)` errors.
3. *Simultaneous coverage.* For `0 < β < 1`, `m = ⌈4·8^k(N + log(1/β) + 1)⌉` independent samples
   from such a measure all miss `L` with probability at most `2^{−N}β`: each fixed target is missed
   with probability at most `2^{−N}β`.

Source: Carlson–Kolla, STOC 2027 submission (manuscript sha256 9b315e04…), Proof of Lemma 6,
*The sampling bodies*, *A volume bound for each target*, *Simultaneous coverage*, p.9.

**Formalization Note.** The orthonormal basis matrix is a linear isometry `W`; `[N]` is `Fin N`;
rounding `Wa` at `1/2` puts `i` in the rounded set iff `(Wa)_i ≥ 1/2` (the margin is `3/8`, so
the other convention gives the same bound); `vol` is Lebesgue measure on `EuclideanSpace ℝ (Fin k)`;
total variation to the uniform law on `K_s` is the supremum over measurable sets; the `m`
independent samples are the product measure `ν^{⊗m}`. The union bound over the `2^N` targets
and the list-size count are not part of this statement. -/
theorem lemma_6_geometry (N k : ℕ) (hN : 1 ≤ N) (hk : 1 ≤ k)
    (W : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N)) :
    let P : Set (EuclideanSpace ℝ (Fin N)) := {x | ∀ i, x.ofLp i ∈ Set.Icc (0 : ℝ) 1}
    let K : ℝ → Set (EuclideanSpace ℝ (Fin k)) := fun s => {a | Metric.infDist (W a) P ^ 2 ≤ s}
    let U : Submodule ℝ (EuclideanSpace ℝ (Fin N)) := LinearMap.range W.toLinearMap
    (∀ j : ℕ, j ≤ Nat.clog 2 N →
      Convex ℝ (K (2 ^ j)) ∧ Metric.closedBall 0 1 ⊆ K (2 ^ j) ∧
        K (2 ^ j) ⊆ Metric.ball 0 (32 * ((N : ℝ) + 1))) ∧
    (∀ (S : Finset (Fin N)) (astar : EuclideanSpace ℝ (Fin k)),
      W astar = U.starProjection (indE S) →
      let D : ℝ := Metric.infDist (indE S) (U : Set (EuclideanSpace ℝ (Fin N))) ^ 2
      let L : ℝ → Set (EuclideanSpace ℝ (Fin k)) :=
        fun s => (fun b => (8 : ℝ)⁻¹ • ((7 : ℝ) • astar + b)) '' K s
      let errs : EuclideanSpace ℝ (Fin k) → ℕ :=
        fun a => #(univ.filter (fun i => ¬ ((1 / 2 : ℝ) ≤ (W a).ofLp i ↔ i ∈ S)))
      (∀ j : ℕ, j ≤ Nat.clog 2 N → max 1 D ≤ (2 : ℝ) ^ j →
        astar ∈ K (2 ^ j) ∧ L (2 ^ j) ⊆ K (2 ^ j) ∧
        volume (L (2 ^ j)) = (8 : ENNReal)⁻¹ ^ k * volume (K (2 ^ j)) ∧
        (∀ a ∈ L (2 ^ j), (errs a : ℝ) ≤ 64 * (2 : ℝ) ^ j / 9) ∧
        (∀ (ν : Measure (EuclideanSpace ℝ (Fin k))) [IsProbabilityMeasure ν],
          (∀ B : Set (EuclideanSpace ℝ (Fin k)), MeasurableSet B →
            |ν.real B - volume.real (B ∩ K (2 ^ j)) / volume.real (K (2 ^ j))| ≤
              (8 : ℝ)⁻¹ ^ k / 4) →
          3 * (8 : ℝ)⁻¹ ^ k / 4 ≤ ν.real (L (2 ^ j)) ∧
          ∀ β : ℝ, 0 < β → β < 1 →
            (Measure.pi (fun _ : Fin ⌈4 * (8 : ℝ) ^ k * ((N : ℝ) + Real.log (1 / β) + 1)⌉₊ => ν)).real
                {x | ∀ i, x i ∉ L (2 ^ j)} ≤ (2 : ℝ)⁻¹ ^ N * β)) ∧
      (∃ j : ℕ, j ≤ Nat.clog 2 N ∧ max 1 D ≤ (2 : ℝ) ^ j ∧ (2 : ℝ) ^ j ≤ 2 * max 1 D ∧
        ∀ a ∈ L (2 ^ j), (errs a : ℝ) ≤ 16 * (D + 1))) := by sorry

end ThreshRankBIS
