-- Prove2me | Theorems.Thm_PrivLearn_SQSim_claim_5_10_estimate
-- name    : PrivLearn.SQSim.claim_5_10_estimate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:47:21.372674+00:00
-- url     : https://prove2.me/theorems/039d1872-d77d-42d3-b214-9111debfc287
-- title:
--   Proof of Claim 5.10, p. 24 — the queries g₁, g₂ estimate p₁, p₂ within (1 ± τ′), τ′ = e^{2ε}τ, and their ratio within (1 ± 3τ′)
-- statement:
--   Let $P$ be a probability distribution on $D$ and $\varepsilon>0$. Let $R_1,\dots,R_m$ and $R_k$ be local randomizers with discrete output set $W$, with budgets $\varepsilon_1,\dots,\varepsilon_m,\varepsilon_k$ satisfying $\varepsilon_1+\dots+\varepsilon_m+\varepsilon_k\le\varepsilon$ and with measurable point probabilities. These are the randomizers applied in turn to one entry; the first $m$ returned $a_1,\dots,a_m$. For an output $w$ and a reference input $u_0$ put
--
--   $$r_1(u)=\Pr[R_k(u)=w]\prod_{j=1}^m\Pr[R_j(u)=a_j],\qquad r_2(u)=\prod_{j=1}^m\Pr[R_j(u)=a_j],\qquad p_i=\mathbb E_{u\sim P}[r_i(u)],$$
--
--   and assume $r_1(u_0)>0$. Let $g_i(u)=\dfrac{r_i(u)-r_i(u_0)}{r_i(u_0)(e^{\varepsilon}-e^{-\varepsilon})}$, let $\tau>0$, $\tau'=e^{2\varepsilon}\tau$, and let $v_1,v_2$ be valid SQ answers to $(g_1,\tau)$ and $(g_2,\tau)$. With $\tilde p_i=v_i\,r_i(u_0)(e^{\varepsilon}-e^{-\varepsilon})+r_i(u_0)$:
--
--   1. $g_1(u),g_2(u)\in[-1,1]$ for every $u$;
--   2. $|\tilde p_1-p_1|\le\tau'p_1$ and $|\tilde p_2-p_2|\le\tau'p_2$;
--   3. if $\tau'\le1/3$, then
--
--   $$\Bigl|\frac{\tilde p_1}{\tilde p_2}-\frac{p_1}{p_2}\Bigr|\le3\tau'\,\frac{p_1}{p_2}.$$
--
--   Here $p_1/p_2$ is the conditional probability that the next randomizer outputs $w$ given the earlier answers on the same entry, so this is the estimate the adaptive simulation of an interactive local algorithm uses for rejection sampling.
--
--   **Formalization Note.** The paper indexes the earlier randomizers $R_1,\dots,R_{k-1}$; here there are $m=k-1$ of them, indexed from $0$. The positivity $r_1(u_0)>0$ is implicit in the paper (it divides by $r_1(\mathbf 0)$ and $r_2(\mathbf 0)$). The paper's input $\mathbf 0$ is an arbitrary $u_0$.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 24, proof of Claim 5.10 (definitions of r_1, r_2, g_1, g_2 and the paragraph "As in Claim 5.9, one can estimate p_1 and p_2 …")

import Mathlib
import Definitions.Def_PrivLearn_SQSim_Privacy
import Definitions.Def_PrivLearn_SQSim_LocalAlg
import Definitions.Def_PrivLearn_SQSim_Estimate

open MeasureTheory

namespace PrivLearn.SQSim

/-- Proof of Claim 5.10 (p. 24): estimating the conditional probability of the next answer on
one entry. The randomizers `R₁, …, R_m` (budgets `ε_j`) were applied to the entry and returned
`a₁, …, a_m`; the next one is `R_k` (budget `ε_k`), and `ε₁ + ⋯ + ε_m + ε_k ≤ ε`. With
`r₁(u) = Pr[R_k(u) = w] ∏_j Pr[R_j(u) = a_j]`, `r₂(u) = ∏_j Pr[R_j(u) = a_j]` and
`p_i = E_{u∼P} r_i(u)`, the queries `g₁, g₂` take values in `[−1, 1]`; for valid answers `v₁, v₂`
with tolerance `τ` the estimates `p̃_i` lie in `(1 ± τ′) p_i`, `τ′ = e^{2ε} τ`; and if `τ′ ≤ 1/3`
their ratio lies in `(1 ± 3τ′) p₁/p₂`. -/
theorem claim_5_10_estimate {Dom W : Type*} [MeasurableSpace Dom] (P : Measure Dom)
    [IsProbabilityMeasure P] (m : ℕ) (Rs : Fin m → Dom → PMF W) (es : Fin m → ℝ)
    (Rk : Dom → PMF W) (ek : ℝ)
    (hmeas_s : ∀ j w, Measurable fun u => Rs j u w) (hmeas_k : ∀ w, Measurable fun u => Rk u w)
    (hloc_s : ∀ j, IsLocalRandomizerPMF (Rs j) (es j)) (hloc_k : IsLocalRandomizerPMF Rk ek)
    (ε : ℝ) (hε : 0 < ε) (hbudget : ∑ j, es j + ek ≤ ε)
    (a : Fin m → W) (w : W) (u₀ : Dom)
    (hpos : 0 < (Rk u₀ w).toReal * ∏ j, (Rs j u₀ (a j)).toReal)
    (τ : ℝ) (hτ : 0 < τ) (v₁ v₂ : ℝ) :
    let r₁ : Dom → ℝ := fun u => (Rk u w).toReal * ∏ j, (Rs j u (a j)).toReal
    let r₂ : Dom → ℝ := fun u => ∏ j, (Rs j u (a j)).toReal
    let p₁ : ℝ := ∫ u, r₁ u ∂P
    let p₂ : ℝ := ∫ u, r₂ u ∂P
    let τ' : ℝ := Real.exp (2 * ε) * τ
    IsSQAnswer P (sqQuery r₁ u₀ ε) τ v₁ → IsSQAnswer P (sqQuery r₂ u₀ ε) τ v₂ →
    (∀ u, sqQuery r₁ u₀ ε u ∈ Set.Icc (-1 : ℝ) 1 ∧ sqQuery r₂ u₀ ε u ∈ Set.Icc (-1 : ℝ) 1) ∧
    |sqEstimate r₁ u₀ ε v₁ - p₁| ≤ τ' * p₁ ∧ |sqEstimate r₂ u₀ ε v₂ - p₂| ≤ τ' * p₂ ∧
    (τ' ≤ 1 / 3 →
      |sqEstimate r₁ u₀ ε v₁ / sqEstimate r₂ u₀ ε v₂ - p₁ / p₂| ≤ 3 * τ' * (p₁ / p₂)) := by sorry

end PrivLearn.SQSim
