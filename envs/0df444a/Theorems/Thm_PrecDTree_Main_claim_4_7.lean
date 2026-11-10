-- Prove2me | Theorems.Thm_PrecDTree_Main_claim_4_7
-- name    : PrecDTree.Main.claim_4_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:51:28.703848+00:00
-- url     : https://prove2.me/theorems/9ace623b-9ad1-4a41-a144-4ed6da9d94ce
-- title:
--   Claim 4.7 — E[Φ] ≥ 0, and Φ ≥ 0 forces blue coverage ≥ t/8 and red cost < 920 · K · γ
-- statement:
--   Let $I=(R,B,\mathcal S,t)$ be a Partial-RBSC instance with $m$ sets, $K$ an integer guess with $1\le K\le|R|$, and $(y,x,z,a,y_{\cdot,\cdot})$ a feasible point of LP (2)–(10) for $K$. For the random construction of the proof of Theorem 4.2 built from this point (activation, trial and marking coins, output $\mathcal C$, red count $R$, marks $M$, $W$, potential $\Phi$ of (14)), in the case $|\mathrm{cov}(\mathcal S_0,B)|<t/8$: $\mathbb E[\Phi]\ge0$; every output $\mathcal C$ of an outcome with $\Phi\ge0$ satisfies $$|\mathrm{cov}(\mathcal C,B)|\ \ge\ t/8\qquad\text{and}\qquad|\mathrm{cov}(\mathcal C,R)|\ <\ 920\cdot K\cdot\gamma;$$ in particular, for the guess $K=\mathrm{OPT}(I)$ the red cost is smaller than $920\cdot\mathrm{OPT}(I)\cdot\gamma$.
--   The claims 4.4–4.7 together show that an outcome with nonnegative potential exists and is a good bicriteria cover; Claim 4.8 finds one deterministically.
--
--   Differences from the source:
--   - generalization: the smallest feasible guess K ≤ OPT(I) with a fixed feasible LP solution → every integer guess K with 1 ≤ K ≤ |R| and every feasible point s of LP (2)–(10) for K; reason: the proof uses only the feasibility of s for K; the paper's guess and solution are one such pair
--   - encoding: independent random events A_{r,d}, T_{r,d,S}, Z_{r,d,S,u} with the stated probabilities → a finite family of independent Bernoulli coins indexed by Coin I (scale d = 2^j indexed by j : Fin k), law the product law prob, E = finite sum expect; coins that do not occur have probability 0; reason: the construction uses finitely many independent coins; this is their joint law
--   - encoding: R⁺ = {r : y_r ≥ 1/γ} → R⁺ = {r : 1 ≤ γ · y_r}; reason: equivalent for γ > 0 (m ≥ 1); for m = 0 it gives R⁺ = ∅, the reading of 1/γ = ∞, instead of Lean's 1/0 = 0
--   - reading: the claim is made in the 'Otherwise' branch, where B' = B \ cov(S₀) and (11) are defined → hypothesis |cov(S₀, B)| < t/8; reason: this is the context the paper states the claim in (p. 10–11)
-- source:
--   Szyfelbein, Dereniowski, Precedence-Constrained Decision Trees and Coverings, arXiv:2602.21312 (STOC 2027 submission version, sha256 aafd336d…), p. 16, Claim 4.7

import Mathlib
import Definitions.Def_PrecDTree_Main_Rounding

set_option autoImplicit false

namespace PrecDTree.Main

/-- **Claim 4.7** (p. 16). In the case `|cov(S₀, B)| < t/8`: `E[Φ] ≥ 0`; every output `C` of an
outcome with `Φ ≥ 0` has `|cov(C, B)| ≥ t/8` and `|cov(C, R)| < 920 · K · γ`; in particular, for
the guess `K = OPT(I)`, the red cost is smaller than `920 · OPT(I) · γ`. -/
theorem claim_4_7 (I : RBInstance) (K : ℕ) (s : LPSol I) (hK : 1 ≤ K) (hKk : K ≤ I.k)
    (hs : LPFeasible I K s) (hS0 : ((I.blueCov (I.S0 s)).card : ℝ) < (I.t : ℝ) / 8) :
    0 ≤ I.expect s (I.Phi s K) ∧
      (∀ ω : I.Coin → Bool, 0 ≤ I.Phi s K ω →
        (I.t : ℝ) / 8 ≤ ((I.blueCov (I.Cout s ω)).card : ℝ) ∧
          ((I.redCov (I.Cout s ω)).card : ℝ) < 920 * (K : ℝ) * I.gamma) ∧
      (K = I.opt → ∀ ω : I.Coin → Bool, 0 ≤ I.Phi s K ω →
        ((I.redCov (I.Cout s ω)).card : ℝ) < 920 * (I.opt : ℝ) * I.gamma) := by sorry

end PrecDTree.Main
