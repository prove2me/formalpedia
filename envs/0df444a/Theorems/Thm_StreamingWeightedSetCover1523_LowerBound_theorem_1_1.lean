-- Prove2me | Theorems.Thm_StreamingWeightedSetCover1523_LowerBound_theorem_1_1
-- name    : StreamingWeightedSetCover1523.LowerBound.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:08:15.465588+00:00
-- url     : https://prove2.me/theorems/ae8cb1d0-3309-46a8-aa68-cd4b95bb9efe
-- title:
--   Theorem 1.1 — two-weight streaming lower bound $pS\ge c\,mk^2/n$
-- statement:
--   There are absolute constants $C_0,c>0$ such that the following holds. Let $\alpha=\alpha(k)\ge1$, and let $M=M(k)$ and $v=v(k)$ be integers with
--   $$M\ge C_0k^2\quad\text{and}\quad 6\alpha e^{27\alpha}k\ln(2M+1)\le v=o(k^2).\qquad(1)$$
--   For all sufficiently large $k$ there is a fixed family $C$ of $M$ weight-one sets covering the universe of $n=2v$ elements such that, on the instances with $m=2M$ sets consisting of $C$ and $M$ transversals of weight $k$ (weights in $\{1,k\}$), every randomized $p$-pass $\alpha$-estimator with $S$ bits of memory that knows $C$ in advance satisfies
--   $$pS\ \ge\ c\,\frac{mk^2}{n}.\qquad(2)$$
--
--   An $\alpha$-estimator outputs after its last pass a number $\widehat{\mathrm{OPT}}$ with $\mathrm{OPT}\le\widehat{\mathrm{OPT}}\le\alpha\,\mathrm{OPT}$ with probability at least $2/3$ on every instance; computation is unrestricted and public and private randomness are allowed. The family is chosen before the estimator, so a single public family defeats every estimator; the threshold in $k$ depends only on the parameter sequences. The source's proof gives $c=1/(1.2\cdot10^6)$.
--
--   Differences from the source:
--   - generalization: p passes over the stream in an arbitrary order fixed across passes, the cheap sets known to the algorithm → p passes over the M expensive vectors in the fixed order E_1, …, E_M; transitions may depend arbitrarily on A, the pass number and the position; reason: an algorithm that must work for every order works for this one; processing the known cheap sets is a fixed function of the state at the start of each pass and is absorbed into the first transition of the pass (or the initial state), with the same p and S
--   - generalization: an α-estimator succeeds with probability ≥ 2/3 on every coverable input with n elements, m sets and weights in {1,k} → success required only on the instances over the fixed family C(A) (all choices of the M transversals); reason: a weaker requirement on the estimator; every source estimator satisfies it, and these are the instances the source proof uses
--   - encoding: randomized algorithm with public and private randomness, S bits of memory → a probability space (Ω, P) of input-independent seeds, each selecting a deterministic machine with state set Fin (2^S); the events in the success requirement are required measurable; reason: pre-drawn seeds cover public and private coins; S bits of persistent state means at most 2^S states; every genuine randomized algorithm has measurable success events
--   - generalization: parameters satisfying (1) (for every k) → (1) and α ≥ 1 required only for all sufficiently large k; reason: the conclusion is asymptotic in k; sequences satisfying (1) for every k satisfy it eventually
--   - encoding: "for sufficiently large C₀ and k", v = o(k²), integers M, v → ∃ C₀ > 0 before all sequences α, M, v : ℕ → ℝ/ℕ; ∀ᶠ k in atTop; v = o(k²) as Asymptotics.IsLittleO; reason: the standing regime of §2 (PDF pp. 7, 11) and Appendix A.2 (PDF p. 22); (1) forces M, v positive on the tail
--   - encoding: OPT, the least weight of a cover → opt in WithTop ℝ, the minimum of the costs of all covers, ⊤ when no cover exists; reason: an exact minimum over a finite set; uncoverable inputs get +∞ instead of a junk value
--   - encoding: vectors in F₂^v, a v×M binary matrix, U=[v]×{0,1}, identifiers C_1..C_M, E_1..E_M, indices 1..M → Fin v → ZMod 2, Fin v → Fin M → Bool, Fin v × ZMod 2, Fin M ⊕ Fin M, 0-based indices (left block = indices 0..r−1); reason: finite relabelling of the same objects; no instance changes
-- source:
--   Ali Vakilian, Streaming Weighted Set Cover Requires (Nearly) Linear Space, STOC 2027 submission #1523 (October 2026), Theorem 1.1, printed p. 2 (PDF p. 3), eqs. (1)–(2); proof printed p. 17 (PDF p. 18); citation basis: submitted artifact, sha256 16f3c2dfc6183f4752aece654f17f2cb6a47fbe55659e6906ad7bd3524d6223f

import Definitions.Def_StreamingWeightedSetCover1523_LowerBound_HardInstance

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

namespace StreamingWeightedSetCover1523.LowerBound

/-- Theorem 1.1 (Two-weight lower bound; PDF p. 3, eqs. (1)–(2)): there are absolute constants
`C₀, c > 0` such that for all sequences `α(k)`, `M(k)`, `v(k)` satisfying (1), for all
sufficiently large `k` there is a fixed cheap family `C(A)` of `M` weight-one sets covering the
universe of `n = 2v` elements such that every randomized `p`-pass `α`-estimator with `S` bits of
memory, knowing `C(A)` in advance, on the instances with `m = 2M` sets and weights in `{1, k}`
satisfies `p S ≥ c m k² / n`. -/
theorem theorem_1_1 :
    ∃ C₀ c : ℝ, 0 < C₀ ∧ 0 < c ∧
      ∀ (α : ℕ → ℝ) (M v : ℕ → ℕ), ParamsEq1 C₀ α M v →
        ∀ᶠ k : ℕ in atTop,
          ∃ A : Mat (v k) (M k), CheapCovers A ∧
            ∀ (p S : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
              (alg : Ω → Machine (M k) (Vec (v k)) (Fin (2 ^ S)) ℝ),
              IsEstimator k (α k) A p P alg →
                c * ((2 * (M k : ℝ)) * (k : ℝ) ^ 2 / (2 * (v k : ℝ))) ≤ (p : ℝ) * (S : ℝ) := by sorry

end StreamingWeightedSetCover1523.LowerBound
