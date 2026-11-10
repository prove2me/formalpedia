-- Prove2me | Theorems.Thm_PrecDTree_Main_claim_4_4
-- name    : PrecDTree.Main.claim_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:51:24.508518+00:00
-- url     : https://prove2.me/theorems/221f18fe-b57a-41f6-9b96-b16423d236ac
-- title:
--   Claim 4.4 — the random construction has expected red cost E[R] ≤ 7 · K · γ
-- statement:
--   Let $I=(R,B,\mathcal S,t)$ be a Partial-RBSC instance with $m$ sets, $K$ an integer guess with $1\le K\le|R|$, and $(y,x,z,a,y_{\cdot,\cdot})$ a feasible point of LP (2)–(10) for $K$. For the random construction of the proof of Theorem 4.2 built from this point (activation, trial and marking coins, output $\mathcal C$, red count $R$, marks $M$, $W$, potential $\Phi$ of (14)), $$\mathbb E[R]\ \le\ 7\cdot K\cdot\gamma,\qquad \gamma=m^{1/3},$$ where $R=|R^+|+|R_0|$ bounds the red cost of the output $\mathcal C$.
--   The claims 4.4–4.7 together show that an outcome with nonnegative potential exists and is a good bicriteria cover; Claim 4.8 finds one deterministically.
--
--   Differences from the source:
--   - generalization: the smallest feasible guess K ≤ OPT(I) with a fixed feasible LP solution → every integer guess K with 1 ≤ K ≤ |R| and every feasible point s of LP (2)–(10) for K; reason: the proof uses only the feasibility of s for K; the paper's guess and solution are one such pair
--   - encoding: independent random events A_{r,d}, T_{r,d,S}, Z_{r,d,S,u} with the stated probabilities → a finite family of independent Bernoulli coins indexed by Coin I (scale d = 2^j indexed by j : Fin k), law the product law prob, E = finite sum expect; coins that do not occur have probability 0; reason: the construction uses finitely many independent coins; this is their joint law
--   - encoding: R⁺ = {r : y_r ≥ 1/γ} → R⁺ = {r : 1 ≤ γ · y_r}; reason: equivalent for γ > 0 (m ≥ 1); for m = 0 it gives R⁺ = ∅, the reading of 1/γ = ∞, instead of Lean's 1/0 = 0
--   - generalization: the claim is made in the 'Otherwise' branch, |cov(S₀, B)| < t/8, where the scales and groups are introduced → no case hypothesis; reason: R, the groups and the activation and trial coins do not depend on B' or (11), and the proof uses only (2), (6), (9), (10); the paper's case is a special case
-- source:
--   Szyfelbein, Dereniowski, Precedence-Constrained Decision Trees and Coverings, arXiv:2602.21312 (STOC 2027 submission version, sha256 aafd336d…), p. 11, Claim 4.4

import Mathlib
import Definitions.Def_PrecDTree_Main_Rounding

set_option autoImplicit false

namespace PrecDTree.Main

/-- **Claim 4.4** (p. 11). For a guess `K ∈ [|R|]` and a feasible point of LP (2)–(10) for `K`, the
random construction satisfies `E[R] ≤ 7 · K · γ`, `γ = m^{1/3}`. -/
theorem claim_4_4 (I : RBInstance) (K : ℕ) (s : LPSol I) (hK : 1 ≤ K) (hKk : K ≤ I.k)
    (hs : LPFeasible I K s) :
    I.expect s (fun ω => (I.Rval s ω : ℝ)) ≤ 7 * (K : ℝ) * I.gamma := by sorry

end PrecDTree.Main
