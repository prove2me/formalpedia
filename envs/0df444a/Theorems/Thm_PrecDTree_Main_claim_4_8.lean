-- Prove2me | Theorems.Thm_PrecDTree_Main_claim_4_8
-- name    : PrecDTree.Main.claim_4_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:53:10.049093+00:00
-- url     : https://prove2.me/theorems/51e9b9ab-e190-482c-b835-c15d69d528ba
-- title:
--   Claim 4.8 — an outcome with Φ ≥ 0 can be found deterministically in polynomial time
-- statement:
--   An outcome with $\Phi\ge0$ can be found deterministically in polynomial time: there is one polynomial-time machine which, given a Partial-RBSC instance $I$, an integer guess $1\le K\le|R|$ and a rational feasible point of LP (2)–(10) for $K$ with $|\mathrm{cov}(\mathcal S_0,B)|<t/8$, outputs an outcome $\omega$ of all the coins of the random construction with
--   $$\Phi(\omega)\ \ge\ 0 .$$
--   This derandomization (method of conditional expectations) turns the expectation bounds of Claims 4.4–4.7 into the deterministic algorithm of Theorem 4.2.
--
--   Differences from the source:
--   - reading: polynomial-time algorithm (no machine model named) → one Mathlib Turing.TM2ComputableInPolyTime machine on binary words (PolyTimeBin), fixed before the instance, required to behave only on codes of valid instances; reason: the standard formal reading of a polynomial-time algorithm; the codes (encNat, incidence bits, tables) are of length polynomial in the input size
--   - generalization: the smallest feasible guess K ≤ OPT(I) with a fixed feasible LP solution → every integer guess K with 1 ≤ K ≤ |R| and every feasible point s of LP (2)–(10) for K; reason: the proof uses only the feasibility of s for K; the paper's guess and solution are one such pair
--   - encoding: independent random events A_{r,d}, T_{r,d,S}, Z_{r,d,S,u} with the stated probabilities → a finite family of independent Bernoulli coins indexed by Coin I (scale d = 2^j indexed by j : Fin k), law the product law prob, E = finite sum expect; coins that do not occur have probability 0; reason: the construction uses finitely many independent coins; this is their joint law
--   - encoding: R⁺ = {r : y_r ≥ 1/γ} → R⁺ = {r : 1 ≤ γ · y_r}; reason: equivalent for γ > 0 (m ≥ 1); for m = 0 it gives R⁺ = ∅, the reading of 1/γ = ∞, instead of Lean's 1/0 = 0
--   - reading: the claim is made in the 'Otherwise' branch, where B' = B \ cov(S₀) and (11) are defined → hypothesis |cov(S₀, B)| < t/8; reason: this is the context the paper states the claim in (p. 10–11)
--   - encoding: a feasible LP solution → a rational LP point LPSolQ I, read by the machine, whose real point is feasible; reason: a machine reads finite data; an LP solver returns rational points
-- source:
--   Szyfelbein, Dereniowski, Precedence-Constrained Decision Trees and Coverings, arXiv:2602.21312 (STOC 2027 submission version, sha256 aafd336d…), p. 16, Claim 4.8

import Mathlib
import Definitions.Def_PrecDTree_Main_Machine

set_option autoImplicit false

namespace PrecDTree.Main

/-- **Claim 4.8** (p. 16). An outcome with `Φ ≥ 0` can be found deterministically in polynomial
time: one polynomial-time machine reads a Partial-RBSC instance, a guess `K ∈ [|R|]` and a rational
feasible point of LP (2)–(10) for `K` with `|cov(S₀, B)| < t/8`, and outputs a coin outcome `ω`
with `Φ(ω) ≥ 0`. -/
theorem claim_4_8 :
    ∃ alg : List Bool → List Bool, PolyTimeBin alg ∧
      ∀ (I : RBInstance) (K : ℕ) (q : LPSolQ I), 1 ≤ K → K ≤ I.k → LPFeasible I K q.toReal →
        ((I.blueCov (I.S0 q.toReal)).card : ℝ) < (I.t : ℝ) / 8 →
        ∃ ω : I.Coin → Bool, alg (encodeRB I ++ encNat K ++ encodeLPQ q) = encodeOutcome I ω ∧
          0 ≤ I.Phi q.toReal K ω := by sorry

end PrecDTree.Main
