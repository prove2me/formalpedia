-- Prove2me | Theorems.Thm_SampQueryLB_WarmSLC_lemma_7_2
-- name    : SampQueryLB.WarmSLC.lemma_7_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:17:32.329085+00:00
-- url     : https://prove2.me/theorems/39930b1f-016e-4e7a-a2e2-29dab468f966
-- title:
--   Lemma 7.2 — Gaussian comparison: $P_w(A)\le3\hat P(A)+Cn^{-1/2}$ against a mean-shifted reference experiment
-- statement:
--   Let $P_w$ be the warm experiment of §7.1: $\Xi\sim\mu_n(\cdot\mid E_n)$, $v$ uniform on $S^{n-1}$, $x^\circ\sim\nu_{\Xi,v}$, a fresh seed independent of $(\Xi,v,x^\circ)$; the algorithm receives $x^\circ$ and first-order oracle access to $V^\Xi_h$, never $v$.
--
--   **Lemma 7.2.** There is a probability law $\lambda_n$ on $\mathbb R^{d_n}$, depending only on the hard family, such that $\zeta_n:=\lambda_n(\mathcal R_n^c)=o(1)$. Fix an algorithm whose number of queries is bounded by a deterministic integer $q$ on every coefficient realization, and consider the reference experiment: (1) draw $x^\circ\sim\lambda_n$ and uniform $v\in S^{n-1}$ independently; (2) independently draw standard Gaussian tensors $\tilde\Xi_{i,p}$ and set $\Xi_{i,p}=\tilde\Xi_{i,p}-\beta_i\Phi_{i,p}(x^\circ)$; (3) give the algorithm $x^\circ$ and oracle access to $V^\Xi_h$, run with an independent fresh seed of the same law, $v$ not revealed. Let $\hat P$ be the joint law of this experiment, including transcript and output. For every measurable event $A$ defined by these variables,
--   $$P_w(A)\le3\hat P(A)+Cn^{-1/2},$$
--   where $C$ is a universal constant.
--
--   **Formalization Note.** The absolute constants $C_f, C_g, \eta_*, \lambda_*$ of the construction are quantified by `ForChosenConstants`: the statement holds for every $C_f\ge C_f^0$, then every $C_g\ge\max(1,C_g^0)$, then every $\eta_*\in(0,\min(1,\eta^0)]$, $\lambda_*\in(0,\min(1/2,\lambda^0)]$ with $\eta_*\lambda_*\le 1/4$ (the order and constraints of the proof of Proposition 4.2), and 'for all sufficiently large $n$' is $\exists n_0\,\forall n\ge n_0$. The family $(\lambda_n)_n$ is chosen after $\vartheta$ and the constants and before the algorithm, $q$ and the event. An event is a measurable set of outcomes $(\Xi,v,x^\circ,\omega,\text{transcript},\text{output})$, the transcript being the number of queries with the history padded to length $q$; $P_w(A)$ and $\hat P(A)$ are the iterated integrals of its indicator (`Pwarm`, `Pref`). "$q$ on every coefficient realization" is $N\le q$ for every $\Xi\in G_n$, initial point and seed.
--
--   Differences from the source:
--   - reading: 'Fix an even function ϑ ∈ C^∞(R; [0,1]) equal to zero for |t| ≤ 9/20 and to one for |t| ≥ 1/2' (§7.1) → ∀ ϑ with IsSlabProfile ϑ, quantified before the constants; reason: the construction fixes an arbitrary such ϑ first; the statement holds for each of them
--   - reading: the absolute constants C_f, C_g, η*, λ* 'can be chosen' / are 'sufficiently large/small', n is 'a sufficiently large integer' (§4.1, proof of Proposition 4.2) → ForChosenConstants: the statement holds for all sufficiently extreme constants in the paper's choice order (C_f, then C_g ≥ 1, then η* ≤ 1, λ* ≤ 1/2, η*λ* ≤ 1/4), and for all n ≥ n0; reason: the paper fixes the constants once by monotone 'sufficiently' conditions; the for-all-sufficiently form implies the paper's existential choice and lets the thresholds of different results be combined
--   - encoding: x = (x_0, …, x_h) ∈ R^{d_n} with blocks x_j ∈ R^n; tensors in R^{n^{pS_i}} with ψ_i = u_i ⊗ u_{i+1}^{⊗K} ⊗ ⋯ → Point (dn n) with block j at coordinates finProdFinEquiv (j, a); G_n = EuclideanSpace on Σ (i,p), (Fin (p·S_i) → Fin n), slot r of ψ_i carrying block i + slotLevel K r; reason: a fixed labelling of coordinates and tensor slots; every statement is invariant under it
--   - reading: 'where C is an absolute (universal) constant' → ∃ C > 0 after the absolute constants C_f, C_g, η*, λ* are chosen and before n; reason: those constants are themselves absolute once chosen, so a constant depending only on them is absolute; C does not depend on n or on anything chosen later
--   - encoding: the §2.2 algorithm: seed ω ∼ Unif[0,1], Borel query maps, stopping sets and output maps, all randomness in ω; in the warm-start model also the initial sample → WarmAlgorithm: measurable maps of ((x_init, ω), history); ω ∈ ℝ with law Unif[0,1] (seedLaw), independent of x_init; reason: the paper's model; maps on all of ℝ restrict to [0,1]
--   - encoding: 'a probability law λ_n … depending only on the hard family, with λ_n(ℛ_n^c) = o(1)'; 'every measurable event A defined by these variables' → ∃ a sequence of probability measures lam n, chosen before the algorithm, with lam n (shell n)ᶜ → 0; every measurable set of outcomes (Ξ, v, x°, ω, padded transcript, output); reason: o(1) is convergence to 0; the outcome tuple carries exactly the variables of the experiment
--   - encoding: joint laws P_w and P̂ → iterated lower integrals of the indicator of the event in the order Ξ, v, x°, ω (P_w) and x°, v, Ξ̃, ω (P̂); reason: Fubini–Tonelli for the measurable events and runs considered
-- source:
--   Zhou, Suzuki, Towards the Query Complexity of Sampling under Strong Log-Concavity and Log-Sobolev Inequalities, arXiv:2611.05813 (held version dated November 3, 2026, sha256 966f8fc0…184c), p. 57, Lemma 7.2 (PDF p. 60)

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_SampQueryLB_WarmSLC_Model
import Definitions.Def_SampQueryLB_WarmSLC_HardFamily
import Definitions.Def_SampQueryLB_WarmSLC_Experiments

open MeasureTheory OAI.LogConcaveSampling ProbabilityTheory Filter
open scoped ENNReal ContDiff RealInnerProductSpace Topology

namespace SampQueryLB.WarmSLC

theorem lemma_7_2 :
    ∀ ϑ : ℝ → ℝ, IsSlabProfile ϑ →
      ForChosenConstants fun c => ∃ C : ℝ, 0 < C ∧
        ∃ lam : (n : ℕ) → Measure (Point (dn n)), (∀ n, IsProbabilityMeasure (lam n)) ∧
          Tendsto (fun n => lam n (shell n)ᶜ) atTop (𝓝 0) ∧
          ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ (q : ℕ) (A : WarmAlgorithm (dn n)),
            (∀ (Ξ : Coef n) (x : Point (dn n)) (w : ℝ), A.numQueries (Vhard c Ξ) x w ≤ q) →
            ∀ Sev : Set (Outcome n q), MeasurableSet Sev →
              Pwarm c ϑ A q Sev ≤
                3 * Pref c (lam n) A q Sev + ENNReal.ofReal (C * (n : ℝ) ^ (-(1 / 2 : ℝ))) := by sorry

end SampQueryLB.WarmSLC
