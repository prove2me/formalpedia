-- Prove2me | Theorems.Thm_SampQueryLB_WarmSLC_lemma_7_3
-- name    : SampQueryLB.WarmSLC.lemma_7_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:17:40.63401+00:00
-- url     : https://prove2.me/theorems/cc7aa287-d439-4914-93cc-1efea20e3965
-- title:
--   Lemma 7.3 — localized query bound: with fewer than $Q$ queries, $\Pr\{G^\Xi_h(Y)>0,\ d_h(Y,x^\circ)\ge\rho_*\}\le n^{-10}$
-- statement:
--   Fix $x^\circ\in\mathcal R_n$ and use the shifted Gaussian coefficients $\Xi_{i,p}=\tilde\Xi_{i,p}-\beta_i\Phi_{i,p}(x^\circ)$ with $\tilde\Xi\sim\mu_n$, without conditioning on $E_n$. Let $\rho_*=P^{-1/16}=Q^{-4}$.
--
--   **Lemma 7.3.** Let an algorithm make fewer than $Q$ first-order queries to $V^\Xi_h$, with a seed independent of the centered coefficients and possibly containing $x^\circ$. Its output $Y$, which need not be a queried point, satisfies
--   $$\Pr\{G^\Xi_h(Y)>0,\ d_h(Y,x^\circ)\ge\rho_*\}\le n^{-10}.$$
--   Gate-success events are declared false when their required directions are undefined.
--
--   **Formalization Note.** The absolute constants $C_f, C_g, \eta_*, \lambda_*$ of the construction are quantified by `ForChosenConstants`: the statement holds for every $C_f\ge C_f^0$, then every $C_g\ge\max(1,C_g^0)$, then every $\eta_*\in(0,\min(1,\eta^0)]$, $\lambda_*\in(0,\min(1/2,\lambda^0)]$ with $\eta_*\lambda_*\le 1/4$ (the order and constraints of the proof of Proposition 4.2), and 'for all sufficiently large $n$' is $\exists n_0\,\forall n\ge n_0$. The algorithm is a §2.2 algorithm started at the fixed point $x^\circ$ with seed $\omega\sim\mathrm{Unif}[0,1]$ independent of $\tilde\Xi$; its maps may use $x^\circ$. "Fewer than $Q$ queries" is $N<Q$ for every coefficient realization and seed. The event also requires $Y_h\neq0$, so that the direction in $d_h(Y,x^\circ)$ is defined.
--
--   Differences from the source:
--   - reading: the absolute constants C_f, C_g, η*, λ* 'can be chosen' / are 'sufficiently large/small', n is 'a sufficiently large integer' (§4.1, proof of Proposition 4.2) → ForChosenConstants: the statement holds for all sufficiently extreme constants in the paper's choice order (C_f, then C_g ≥ 1, then η* ≤ 1, λ* ≤ 1/2, η*λ* ≤ 1/4), and for all n ≥ n0; reason: the paper fixes the constants once by monotone 'sufficiently' conditions; the for-all-sufficiently form implies the paper's existential choice and lets the thresholds of different results be combined
--   - encoding: x = (x_0, …, x_h) ∈ R^{d_n} with blocks x_j ∈ R^n; tensors in R^{n^{pS_i}} with ψ_i = u_i ⊗ u_{i+1}^{⊗K} ⊗ ⋯ → Point (dn n) with block j at coordinates finProdFinEquiv (j, a); G_n = EuclideanSpace on Σ (i,p), (Fin (p·S_i) → Fin n), slot r of ψ_i carrying block i + slotLevel K r; reason: a fixed labelling of coordinates and tensor slots; every statement is invariant under it
--   - encoding: the §2.2 algorithm: seed ω ∼ Unif[0,1], Borel query maps, stopping sets and output maps, all randomness in ω; in the warm-start model also the initial sample → WarmAlgorithm: measurable maps of ((x_init, ω), history); ω ∈ ℝ with law Unif[0,1] (seedLaw), independent of x_init; reason: the paper's model; maps on all of ℝ restrict to [0,1]
--   - encoding: probabilities of events of the run → the measure (outer measure) of the corresponding set; reason: the run is a Borel function of its inputs, so these sets are measurable; an outer-measure upper bound is at least as strong
--   - encoding: a seed independent of the centered coefficients, possibly containing x°, in any standard Borel space → the input x° is given to every map and the seed is ω ∼ Unif[0,1] independent of Ξ̃; reason: every law on a standard Borel space is the image of Unif[0,1] under a Borel map, which the algorithm's maps can absorb
--   - encoding: 'Gate-success events are declared false when their required directions are undefined' → the event includes Y_h ≠ 0; reason: d_h(Y, x°) uses the direction of Y_h; x° ∈ ℛ_n has all blocks nonzero
-- source:
--   Zhou, Suzuki, Towards the Query Complexity of Sampling under Strong Log-Concavity and Log-Sobolev Inequalities, arXiv:2611.05813 (held version dated November 3, 2026, sha256 966f8fc0…184c), p. 58, Lemma 7.3 (PDF p. 61)

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_SampQueryLB_WarmSLC_Model
import Definitions.Def_SampQueryLB_WarmSLC_HardFamily
import Definitions.Def_SampQueryLB_WarmSLC_Experiments

open MeasureTheory OAI.LogConcaveSampling ProbabilityTheory Filter
open scoped ENNReal ContDiff RealInnerProductSpace Topology

namespace SampQueryLB.WarmSLC

theorem lemma_7_3 :
    ForChosenConstants fun c => ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      ∀ x0 ∈ shell n, ∀ A : WarmAlgorithm (dn n),
        (∀ (Ξ : Coef n) (w : ℝ), A.numQueries (Vhard c Ξ) x0 w < QQ n) →
        ((mu n).prod seedLaw)
            {z | 0 < gate c (z.1 - shift c x0) (lastLvl n) (A.output (Vhard c (z.1 - shift c x0)) x0 z.2) ∧
              blk (A.output (Vhard c (z.1 - shift c x0)) x0 z.2) (lastLvl n) ≠ 0 ∧
              rhoStar n ≤
                dproj (lastLvl n) (A.output (Vhard c (z.1 - shift c x0)) x0 z.2) x0} ≤
          ENNReal.ofReal (((n : ℝ) ^ 10)⁻¹) := by sorry

end SampQueryLB.WarmSLC
