-- Prove2me | Theorems.Thm_StreamingWeightedSetCover1523_LowerBound_lemma_4_1
-- name    : StreamingWeightedSetCover1523.LowerBound.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:08:10.822894+00:00
-- url     : https://prove2.me/theorems/c5a7ad12-f891-47e4-bab5-1a549859e2ff
-- title:
--   Lemma 4.1 — public-family streaming gap hardness (14)
-- statement:
--   There is an absolute constant $C_0>0$ (the constant of (1)) with the following property. Let $\gamma\in(0,1/2]$ be a constant and let the sequences $\alpha(k),M(k),v(k)$ satisfy (1) and, in addition, $M\ge(4/\gamma)k^2$ for all large $k$. For all sufficiently large $k$, with probability at least $4/5$ over the draw of $A$, the family $C=C(A)$ covers $U$ and every randomized $p$-pass streaming algorithm with $S$ bits of memory that solves the gap problem for $C$ with advantage $\gamma$ satisfies
--   $$pS\ \ge\ \frac{\gamma}{2\cdot10^5}\cdot\frac{mk^2}{n},\qquad m=2M,\ n=2v.\qquad(14)$$
--
--   In the gap problem only the $M$ transversals are streamed; the algorithm knows $C$ and may depend on it arbitrarily, and must answer YES when $\mathrm{OPT}\le3k$ and NO when $\mathrm{OPT}>3\alpha k$, each with probability at least $1/2+\gamma$. The good family is chosen before the algorithm; one family defeats every algorithm with the stated resources.
--
--   Differences from the source:
--   - generalization: p passes over the stream in an arbitrary order fixed across passes, the cheap sets known to the algorithm → p passes over the M expensive vectors in the fixed order E_1, …, E_M; transitions may depend arbitrarily on A, the pass number and the position; reason: an algorithm that must work for every order works for this one; processing the known cheap sets is a fixed function of the state at the start of each pass and is absorbed into the first transition of the pass (or the initial state), with the same p and S
--   - encoding: randomized algorithm with public and private randomness, S bits of memory → a probability space (Ω, P) of input-independent seeds, each selecting a deterministic machine with state set Fin (2^S); the events in the success requirement are required measurable; reason: pre-drawn seeds cover public and private coins; S bits of persistent state means at most 2^S states; every genuine randomized algorithm has measurable success events
--   - generalization: parameters satisfying (1) (for every k) → (1) and α ≥ 1 required only for all sufficiently large k; reason: the conclusion is asymptotic in k; sequences satisfying (1) for every k satisfy it eventually
--   - encoding: "for sufficiently large C₀ and k", v = o(k²), integers M, v → ∃ C₀ > 0 before all sequences α, M, v : ℕ → ℝ/ℕ; ∀ᶠ k in atTop; v = o(k²) as Asymptotics.IsLittleO; reason: the standing regime of §2 (PDF pp. 7, 11) and Appendix A.2 (PDF p. 22); (1) forces M, v positive on the tail
--   - encoding: probability over the draw of A with independent Bernoulli(4/k) entries → probA: the finite sum of the product weights ∏(4/k or 1−4/k) over the matrices in the event; reason: the exact law of A on the finite set of matrices
--   - encoding: OPT, the least weight of a cover → opt in WithTop ℝ, the minimum of the costs of all covers, ⊤ when no cover exists; reason: an exact minimum over a finite set; uncoverable inputs get +∞ instead of a junk value
--   - encoding: vectors in F₂^v, a v×M binary matrix, U=[v]×{0,1}, identifiers C_1..C_M, E_1..E_M, indices 1..M → Fin v → ZMod 2, Fin v → Fin M → Bool, Fin v × ZMod 2, Fin M ⊕ Fin M, 0-based indices (left block = indices 0..r−1); reason: finite relabelling of the same objects; no instance changes
-- source:
--   Ali Vakilian, Streaming Weighted Set Cover Requires (Nearly) Linear Space, STOC 2027 submission #1523 (October 2026), Lemma 4.1, printed pp. 15–16 (PDF pp. 16–17), eq. (14); proof PDF pp. 17–18; citation basis: submitted artifact, sha256 16f3c2dfc6183f4752aece654f17f2cb6a47fbe55659e6906ad7bd3524d6223f

import Definitions.Def_StreamingWeightedSetCover1523_LowerBound_HardInstance

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

namespace StreamingWeightedSetCover1523.LowerBound

/-- Lemma 4.1 (PDF pp. 15–16, eq. (14)): there is an absolute `C₀ > 0` (the constant of (1)) such
that for every constant `γ ∈ (0, 1/2]` and all parameter sequences satisfying (1) and eventually
`M ≥ (4/γ) k²`, for all sufficiently large `k`, with probability at least `4/5` over the draw of
`A`, the family `C(A)` covers `U` and every randomized `p`-pass streaming algorithm with `S` bits
of memory that solves the gap problem for `C(A)` with advantage `γ` satisfies
`p S ≥ (γ / (2·10⁵)) · m k² / n`, with `m = 2M`, `n = 2v`. -/
theorem lemma_4_1 :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ γ : ℝ, 0 < γ → γ ≤ 1 / 2 →
        ∀ (α : ℕ → ℝ) (M v : ℕ → ℕ), ParamsEq1 C₀ α M v →
          (∀ᶠ k : ℕ in atTop, (4 / γ) * (k : ℝ) ^ 2 ≤ (M k : ℝ)) →
            ∀ᶠ k : ℕ in atTop,
              (4 / 5 : ℝ) ≤ probA k (fun A : Mat (v k) (M k) =>
                CheapCovers A ∧
                  ∀ (p S : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
                    [IsProbabilityMeasure P]
                    (alg : Ω → Machine (M k) (Vec (v k)) (Fin (2 ^ S)) Bool),
                    SolvesGap k (α k) γ A p P alg →
                      γ / (2 * 10 ^ 5) * ((2 * (M k : ℝ)) * (k : ℝ) ^ 2 / (2 * (v k : ℝ))) ≤
                        (p : ℝ) * (S : ℝ)) := by sorry

end StreamingWeightedSetCover1523.LowerBound
