-- Prove2me | Theorems.Thm_RandKSATSample_Main_proposition_6_2
-- name    : RandKSATSample.Main.proposition_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:02:34.058501+00:00
-- url     : https://prove2.me/theorems/9e700ca8-7135-48e7-acee-8fb463a71394
-- title:
--   Proposition 6.2 — approximate core heat-bath update: a.s. termination, TV ≤ r_iζ/a_i from π(· | σ_{−i}), expected cost ≤ 2C_i/(1 − x)^{r_i}
-- statement:
--   Let $\Phi$ be a nice formula (Condition 3.12), $\sigma\in\Omega$ a feasible core assignment, $B_i$ a core block, $r_i=|J_i|$ the number of mixed clauses incident to $B_i$, $x=e\,p_*$ and $a_i=(1-x)^{r_i}$. One trial of CoreHeatBath$(\sigma,i;\zeta)$ (Definition 6.1) draws a uniform candidate $z\in\Omega_i$ and tests the clauses $a_1,\dots,a_\ell$ of $L_{i,\sigma}(z)$ in turn with coins of probabilities $\hat\nu_j(z)\in[0,1]$ satisfying $|\hat\nu_j(z)-\nu_j(z)|\le\zeta$, where $\nu_j=\mu_{F_{j-1}}(B_{a_j})$ is the ideal violation probability; the trial accepts $z$ with probability $\prod_j(1-\hat\nu_j(z))/|\Omega_i|$ and has expected cost at most $C_i$. If $\zeta\ge0$ and $r_i\zeta\le a_i/2$, the procedure that repeats independent trials until acceptance terminates almost surely, its output $\sigma'_i$ satisfies
--   $$\big\|\mathrm{Law}(\sigma'_i\mid\sigma)-\pi(\cdot\mid\sigma_{-i})\big\|_{TV}\le\frac{r_i\zeta}{a_i},$$
--   and its expected total cost, every rejected trial included, is at most $2C_i/(1-x)^{r_i}$. For CoreHeatBath, $C_i=\tilde O(U_i+(r_i+1)T_{\mathrm{coin}}(\zeta))$, which gives the printed cost bound. This is the accuracy and cost guarantee of one approximate block update of the core chain, which the proof of Theorem 1.1 composes with the spectral gap of Theorem 4.1.
--
--   Differences from the source:
--   - generalization: coins of LocalMarginalCoin_K with cutoff K ≤ r, candidates from the rejection sampler of Lemma 3.7, test order unspecified, ζ > 0 → any trial whose acceptance law is ∏_j(1 − ν̂_j(z))/|Ω_i| with coin probabilities ν̂_j(z) ∈ [0, 1] within ζ of the ideal ν_j, any order of L_{i,σ}(z), any bound C on the expected cost of one trial, ζ ≥ 0; reason: the proof (pp. 57–58) uses only these properties (|ν̂_j − ν_j| ≤ ζ comes from Propositions 5.11, 5.14 and K ≤ r); CoreHeatBath(σ, i; ζ) is an instance
--   - reading: E[Cost] ≤ Õ((U_i + (r_i+1)T_coin(ζ))/(1 − x)^{r_i}) → expected total cost ≤ 2C/(1 − x)^{r_i} with C the expected cost of one trial; reason: the proof's explicit bound 2C_i/a_i (p. 58) with C_i = Õ(U_i + (r_i+1)T_coin(ζ)); the Õ is in C_i
--   - reading: r_i the number of mixed clauses incident to B_i → |J_i|, J_i = {a ∈ C_good : vbl(C_a) ∩ B_i ≠ ∅}; reason: a good clause meeting a core block has both good and bad variables, and §6.1 (p. 56) works with this J_i
--   - encoding: the §6 standing assumption (p. 56) that Φ is nice and σ is feasible → hypotheses Nice Φ and σ ∈ Ω; block index i → the component B_i itself; reason: Lean needs them as binders
--   - encoding: termination almost surely; Law(σ′_i | σ) → procHaltProb = 1; procOut, the probability of returning each z, as sup over time; reason: the procedure as a Markov chain on (outcome, accumulated cost)
-- source:
--   He, Li, Yang, Fast Almost-Uniform Sampling of Random k-SAT Solutions, arXiv:2610.10474 (version not printed; file sha256 563a4d84…), pp. 57–58, Proposition 6.2

import Mathlib
import Definitions.Def_RandKSATSample_Main_TrialScheme
import Definitions.Def_IsingLTL_BeliefProp_TVDist

set_option autoImplicit false

open scoped ENNReal

namespace RandKSATSample.Main

/-- Proposition 6.2 (the core heat-bath update): let `Φ` be nice, `σ ∈ Ω` a feasible core
assignment, `B_i` a core block, `r_i = |J_i|` the number of mixed clauses incident to `B_i`,
`x = e p∗` and `a_i = (1 − x)^{r_i}`. One trial of the update draws a uniform candidate
`z ∈ Ω_i` and tests the clauses of `L_{i,σ}(z)`, in an order `a_1, …, a_ℓ`, with coins of
probabilities `ν̂_j(z) ∈ [0, 1]` within `ζ` of the ideal `ν_j = µ_{F_{j−1}}(B_{a_j})`; it accepts
`z` with probability `Π_j (1 − ν̂_j(z))/|Ω_i|` and has expected cost at most `C`. If
`r_i ζ ≤ a_i/2`, the procedure that repeats trials until acceptance terminates almost surely, its
output law is within total variation `r_i ζ/a_i` of `π(· | σ_{−i})`, and its expected total cost,
rejected trials included, is at most `2C/a_i`. -/
theorem proposition_6_2 {n m k : ℕ} (Φ : Formula n m k) (hnice : Nice Φ)
    (σ : BadAssign Φ) (hσ : σ ∈ Omega Φ) (B : Finset (Fin n)) (hB : B ∈ blocks Φ)
    (ζ C : ℝ) (hζ : 0 ≤ ζ) (hC : 0 ≤ C)
    (hsmall : ((Jblk Φ B).card : ℝ) * ζ ≤ (1 - xpar k) ^ (Jblk Φ B).card / 2)
    (ord : {z // z ∈ OmegaBlock Φ B} → List (Fin m))
    (hord : ∀ z, (ord z).Nodup ∧ (ord z).toFinset = Lset Φ σ B z.1)
    (νhat : {z // z ∈ OmegaBlock Φ B} → ℕ → ℝ)
    (hνhat : ∀ z, ∀ j < (ord z).length, 0 ≤ νhat z j ∧ νhat z j ≤ 1)
    (hclose : ∀ z, ∀ j < (ord z).length, |νhat z j - nuTest Φ σ B (ord z) j| ≤ ζ)
    (trial : PMF (Option {z // z ∈ OmegaBlock Φ B} × ℕ))
    (hlaw : ∀ z, (trial.map Prod.fst) (some z) =
      ENNReal.ofReal (acceptProb (fun z => (ord z).length) νhat z /
        ((OmegaBlock Φ B).card : ℝ)))
    (hcost : ∑' s, trial s * (s.2 : ℝ≥0∞) ≤ ENNReal.ofReal C) :
    procHaltProb trial = 1 ∧
    IsingLTL.BeliefProp.tvDist (condBlockLaw Φ σ B) (procOut trial) ≤
      ((Jblk Φ B).card : ℝ) * ζ / (1 - xpar k) ^ (Jblk Φ B).card ∧
    procExpCost trial ≤ ENNReal.ofReal (2 * C / (1 - xpar k) ^ (Jblk Φ B).card) := by sorry

end RandKSATSample.Main
