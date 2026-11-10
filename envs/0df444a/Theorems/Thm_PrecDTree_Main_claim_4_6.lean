-- Prove2me | Theorems.Thm_PrecDTree_Main_claim_4_6
-- name    : PrecDTree.Main.claim_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:51:36.89258+00:00
-- url     : https://prove2.me/theorems/a24b2e86-eb19-43bb-bebc-3f03644e76b2
-- title:
--   Claim 4.6 — the second moment of the mark count is E[W²] ≤ 10 t²
-- statement:
--   Let $I=(R,B,\mathcal S,t)$ be a Partial-RBSC instance with $m$ sets, $K$ an integer guess with $1\le K\le|R|$, and $(y,x,z,a,y_{\cdot,\cdot})$ a feasible point of LP (2)–(10) for $K$. For the random construction of the proof of Theorem 4.2 built from this point (activation, trial and marking coins, output $\mathcal C$, red count $R$, marks $M$, $W$, potential $\Phi$ of (14)), in the case $|\mathrm{cov}(\mathcal S_0,B)|<t/8$, the count $W=\sum_{r,d}W_{r,d}$ of marks with multiplicity satisfies $$\mathbb E[W^2]\ \le\ 10\cdot t^2.$$
--   The claims 4.4–4.7 together show that an outcome with nonnegative potential exists and is a good bicriteria cover; Claim 4.8 finds one deterministically.
--
--   Differences from the source:
--   - generalization: the smallest feasible guess K ≤ OPT(I) with a fixed feasible LP solution → every integer guess K with 1 ≤ K ≤ |R| and every feasible point s of LP (2)–(10) for K; reason: the proof uses only the feasibility of s for K; the paper's guess and solution are one such pair
--   - encoding: independent random events A_{r,d}, T_{r,d,S}, Z_{r,d,S,u} with the stated probabilities → a finite family of independent Bernoulli coins indexed by Coin I (scale d = 2^j indexed by j : Fin k), law the product law prob, E = finite sum expect; coins that do not occur have probability 0; reason: the construction uses finitely many independent coins; this is their joint law
--   - encoding: R⁺ = {r : y_r ≥ 1/γ} → R⁺ = {r : 1 ≤ γ · y_r}; reason: equivalent for γ > 0 (m ≥ 1); for m = 0 it gives R⁺ = ∅, the reading of 1/γ = ∞, instead of Lean's 1/0 = 0
--   - reading: the claim is made in the 'Otherwise' branch, where B' = B \ cov(S₀) and (11) are defined → hypothesis |cov(S₀, B)| < t/8; reason: this is the context the paper states the claim in (p. 10–11)
-- source:
--   Szyfelbein, Dereniowski, Precedence-Constrained Decision Trees and Coverings, arXiv:2602.21312 (STOC 2027 submission version, sha256 aafd336d…), p. 14, Claim 4.6

import Mathlib
import Definitions.Def_PrecDTree_Main_Rounding

set_option autoImplicit false

namespace PrecDTree.Main

/-- **Claim 4.6** (p. 14). In the case `|cov(S₀, B)| < t/8`, `E[W²] ≤ 10 · t²`. -/
theorem claim_4_6 (I : RBInstance) (K : ℕ) (s : LPSol I) (hK : 1 ≤ K) (hKk : K ≤ I.k)
    (hs : LPFeasible I K s) (hS0 : ((I.blueCov (I.S0 s)).card : ℝ) < (I.t : ℝ) / 8) :
    I.expect s (fun ω => (I.Wval s ω : ℝ) ^ 2) ≤ 10 * (I.t : ℝ) ^ 2 := by sorry

end PrecDTree.Main
