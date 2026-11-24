-- Prove2me | Theorems.Thm_SeqDiagnosis_BeliefRecon_Supplement_theorem_3
-- name    : SeqDiagnosis.BeliefRecon.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:24:49.144133+00:00
-- url     : https://prove2.me/theorems/a53f73fc-824b-47f8-8252-22c121bd4ca9
-- title:
--   Theorem 3, p. 18 — finite critical stopping time if $c>(\bar n_s-1)/\bar n_s$, and time 0 if $c\ge N/(N+1)$ (corrected: $n_s$ over $\mathbb R^r$ in the first clause)
-- statement:
--   Consider the infinite-horizon problem ($T=\infty$) with the uninformative prior $\theta_i=1/(N+1)$, $i\in\mathcal N$, and the zero-one cost structure $a_{ii}=0$, $a_{ij}=1$ ($j\ne i$), $c_i=c\ge0$. The class densities satisfy the exponential tilting model (2) with a rank decomposition $\mathbb B=\mathbb R\mathbb P$ ($\mathbb R$ of full column rank $r$, $\mathbb P$ of full row rank $r$). Let $V_\infty=\inf_kW_k$ be the infinite-horizon optimal cost, the infimum of the finite-horizon values over horizons. A period $t_c$ is a critical stopping time if, at every belief $\Pi_{t_c}$ reachable from the prior after $t_c$ observations,
--
--   $$\min_jV^j(\Pi_{t_c})\le c+\int V_\infty\bigl(\mathcal B(\Pi_{t_c},y)\bigr)\,\Pi_{t_c}F(y)\,d\mu(y),$$
--
--   that is, the waiting region is empty and the decision process must terminate. With $g_0=0$ and $g_i(x)=\beta_{i0}+e_i\mathbb Rx$, let $n_s=\max_{t\ge1,\,x\in\Omega_t}|\{g_i(x),i\in\mathcal N\}|$ be the degree of confusion of §4.2 and $\bar n_s=\max_{x\in\mathbb R^r}|\{g_i(x),i\in\mathcal N\}|$ the same maximum over all of $\mathbb R^r$. Assume $n_s\ge2$ (endnote 4). Then:
--
--   1. If $c>(\bar n_s-1)/\bar n_s$, there exists a finite critical stopping time $t_c\in\mathbb N$.
--   2. If $c\ge N/(N+1)$, then $t_c=0$ is a critical stopping time: it is optimal to diagnose at once.
--
--   Multi-class diagnosis can thus have a deterministic bound on the stopping time, unlike two-class diagnosis. The first clause is stated with $\bar n_s$ in place of the printed $n_s$: as printed (with $n_s$ taken over the attained statistics only), it fails; a counterexample with $N=2$, $n_s=2$, $c=0.55$ is recorded with the mission.
--
--   Differences from the source:
--   - reading: class densities f_0,…,f_N on 𝒴 satisfying (2) → the published base Model with M.Standing and M.ETM (f₀ > 0 on Y, ∫ f₀ dμ = 1, measurable densities, integrable tilts); reason: inherited unchanged from the published base mission, where 𝒴 is read as the support of f₀ and each f_i is a probability density; the integrals in (1) need these to be finite
--   - generalization: observations in a set 𝒴 of the real line, integrals dy → observations in any measurable type Y, integrals against the base reference measure μ; reason: specializes to 𝒴 ⊂ ℝ with Lebesgue measure (continuous case) or counting measure (discrete case, which the paper also allows, p. 6)
--   - correction: c > (nₛ − 1)/nₛ with nₛ the maximum over attained x ∈ Ωt, t ≥ 1 → c > (n̄ₛ − 1)/n̄ₛ with n̄ₛ the same maximum over every x ∈ ℝʳ (confusionAll); reason: as printed the clause is false: on 𝒴 = (0,1) with h(y) = (y, y²), N = 2, the three exponents coincide only at the unattained point h(0), so nₛ = 2, yet statistics h(ε) give near-uniform posteriors at every t, and with c = 0.55 waiting is strictly better there (DISPROOF.md); EC.7 (p. ec27) obtains its threshold t′ separately for each x, so the uniformity in x is not proved; over ℝʳ every set of n̄ₛ + 1 exponents is separated by a uniform gap and the uniform bound holds; endnote 4 describes nₛ as the number of densities intersecting at the same point, without reachability. Excluded: models with n̄ₛ > nₛ and c ∈ ((nₛ−1)/nₛ, (n̄ₛ−1)/n̄ₛ]
--   - reading: infinite-horizon value R⋆ (infimum of expected costs over admissible policies, T = ∞) → valueInf = infimum over horizons k of the finite-horizon values W_k; reason: the paper solves Theorem 3 only through the optimality equations; with bounded nonnegative costs truncating a policy at a deadline changes its cost by at most a vanishing amount, so the two values agree
--   - reading: a finite critical stopping time at which the decision process must terminate → ∃ tc : ℕ such that at every belief reachable after exactly tc observations min_j V^j ≤ waiting value (ties count as stopping); reason: the definition on pp. 15 and 17: a period at which the waiting region is empty and all sample paths are cut off
--   - reading: endnote 4: only cases with nₛ ⩾ 2 are considered → hypothesis 2 ≤ confusion M R P; reason: the paper's own scope restriction for Theorem 3
-- source:
--   Wang, Optimal Sequential Multi-class Diagnosis, arXiv:1506.08915v4, p. 18 (PDF 18), Theorem 3; degree of confusion p. 18 and endnote 4, p. 34 (PDF 34); proof in EC.7, pp. ec26–ec27 (PDF 63–64)

import Mathlib
import Definitions.Def_SeqDiagnosis_BeliefRecon_Supplement_Critical

namespace SeqDiagnosis.BeliefRecon.Supplement

/-- Theorem 3 (corrected: the degree of confusion in the first clause is taken over every
`x ∈ ℝʳ`): infinite horizon, uniform prior, zero-one costs with delay cost `c`. -/
theorem theorem_3 {Y : Type*} [MeasurableSpace Y] {N p r : ℕ}
    (M : Model Y N p) (hS : M.Standing) (hETM : M.ETM)
    (R : Matrix (Fin N) (Fin r) ℝ) (P : Matrix (Fin r) (Fin p) ℝ)
    (hRP : M.Bmat = R * P) (hR : R.rank = r) (hP : P.rank = r)
    (c : ℝ) (hc : 0 ≤ c) (hns : 2 ≤ confusion M R P) :
    ((((confusionAll M R P : ℕ) : ℝ) - 1) / (confusionAll M R P : ℝ) < c →
      ∃ tc : ℕ, IsCriticalTime M (zeroOne N c) (uniformPrior N) tc) ∧
    ((N : ℝ) / ((N : ℝ) + 1) ≤ c → IsCriticalTime M (zeroOne N c) (uniformPrior N) 0) := by sorry

end SeqDiagnosis.BeliefRecon.Supplement
