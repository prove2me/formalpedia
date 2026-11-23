-- Prove2me | Theorems.Thm_WiesemannRMDP_SRect_Supplement_theorem_5_3
-- name    : WiesemannRMDP.SRect.Supplement.theorem_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:54:03.217621+00:00
-- url     : https://prove2.me/theorems/5df81622-1a1b-41b9-b630-f415630d3105
-- title:
--   Theorem 5.3 — under (A1)–(A3) the likelihood ratio 2[ℓ_n(ξ^n) − ℓ_n(ξ^0)] converges in distribution to χ²_κ
-- statement:
--   Let the structural model $\Xi_0$, $p^\xi(\cdot\mid s,a)=k_{sa}+K_{sa}\xi$ satisfy the standing assumptions (3), let $\xi^0\in\Xi_0$ be the true parameter and $\pi_0$ the known historical stationary policy, and let $(s_t,a_t)_{t\ge1}$ be the observation process: the state-action Markov chain of the MDP under $\pi_0$ and $p^{\xi^0}$ started from $p_0$. Let $\ell_n$ be the log-likelihood (33) of the observation $(s_1,a_1,\dots,s_n,a_n)$, with $\log 0=-\infty$, and $\ell_n(\xi^n)=\max_{\xi\in\Xi_0}\ell_n(\xi)$ its maximum. Let $\kappa$ be the rank of the matrix with rows $[K_{sa}]^\top_{s'\cdot}$, $\pi_0(a\mid s)>0$.
--
--   Under the assumptions (A1) $\xi^0\in\operatorname{int}\Xi_0$, (A2) $\widehat P(\pi_0;\xi)$ is irreducible for some $\xi\in\Xi_0$, and (A3) $\kappa>0$,
--   $$2\big[\ell_n(\xi^n)-\ell_n(\xi^0)\big]\ \xrightarrow[n\to\infty]{\ d\ }\ \chi^2_\kappa, \tag{35}$$
--   where $\xrightarrow{d}$ is convergence in distribution and $\chi^2_\kappa$ is the $\chi^2$-distribution with $\kappa$ degrees of freedom.
--
--   Setting $\delta$ in (34) to half the $(1-\beta)$-quantile of $\chi^2_\kappa$ therefore yields an asymptotic $(1-\beta)$-confidence region for $\xi^0$.
--
--   **Formalization Note** Convergence in distribution is Mathlib's `TendstoInDistribution`: the statistics are almost-everywhere measurable and their laws converge weakly to $\chi^2_\kappa$, the law of the sum of $\kappa$ squared independent standard normals. The statistic converts both log-likelihoods to real numbers; almost surely both are finite and it equals the paper's statistic.
--
--   Differences from the source:
--
--   - generalization: (Ω, F, P) is the canonical space (S × A)^∞ with the product σ-field and the measure induced by π0 and P0 → any probability space with a process whose finite paths have the probabilities (32) at ξ0; reason: the conclusion depends only on the law of the observations, and the canonical space is one such space
--   - encoding: 2[ℓn(ξn) − ℓn(ξ0)] with values in ℝ ∪ {−∞} → the difference of the real parts of the two log-likelihoods; reason: both are finite almost surely (the observed path has positive probability, p. 31), so the laws coincide
--   - encoding: the observation (s1, a1, …, sn, an) → X 0, …, X (n − 1); reason: Lean's time index starts at 0
--   - encoding: ℓn(ξn) for a maximum likelihood estimator ξn → the supremum of ℓn over Ξ0 in the extended reals; reason: the maximum is attained (p. 31), so its value is the supremum whichever maximizer is chosen
--   - reading: "the MDP" of §5.1 satisfies definition (3) → the whole of Model.Standing is assumed; reason: r, λ do not occur in Theorem 5.3 (p. 33: "We do not specify a discount factor λ or one-step rewards r since they are irrelevant for Theorem 5.3"), so no instance is lost
-- source:
--   Wiesemann, Kuhn & Rustem, Robust Markov Decision Processes, Optimization Online 2610 (revision of February 9, 2012; sha256 8cbadb80…a79b), p. 32, Theorem 5.3 (35); (30) pp. 28–29; (A1) p. 29; (33) p. 31; (A2), (A3) p. 32; proof Appendix B pp. 46–48

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_WiesemannRMDP_SRect_Model
import Definitions.Def_WiesemannRMDP_SRect_Supplement_Chains
import Definitions.Def_WiesemannRMDP_SRect_Supplement_Inference

open MeasureTheory ProbabilityTheory Filter FoundationsML.ReinforcementLearning Matrix
open scoped Topology ENNReal

namespace WiesemannRMDP.SRect.Supplement

open WiesemannRMDP.SRect

/-- Theorem 5.3 (Wiesemann, Kuhn & Rustem, *Robust Markov Decision Processes*, Optimization
Online 2610, revision of February 9, 2012, p. 32): under the assumptions (A1)–(A3),
`2 [ℓ_n(ξ_n) − ℓ_n(ξ0)] → χ²_κ` in distribution as `n → ∞` (35), where `κ` is the rank in (A3).

Here `X` is the observation process of the MDP under the historical policy `π0` and the true
parameter `ξ0` (§5, pp. 28–29), `ℓ_n` is the log-likelihood (33) of its first `n` state-action
pairs and `ℓ_n(ξ_n) = max_{ξ ∈ Ξ0} ℓ_n(ξ)`.

**Formalization Note.** Convergence in distribution is Mathlib's `TendstoInDistribution`: weak
convergence of the laws of the statistics (which includes their almost-everywhere measurability)
to the law `chiSquared κ` of the identity on `ℝ`. The statistic is `lrStat`; it is the
paper's quantity almost surely (see `lrStat`). -/
theorem theorem_5_3 {St Act : Type*} [Fintype St] [DecidableEq St] [Fintype Act]
    [DecidableEq Act] [Nonempty St] [Nonempty Act] {q L : ℕ} (M : Model St Act q L)
    (hM : M.Standing) (π0 : St → Act → ℝ) (hπ0 : IsPolicy π0)
    (ξ0 : Fin q → ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → St × Act) (hX : IsObservationProcess M π0 ξ0 P X)
    (hA1 : A1 M ξ0) (hA2 : A2 M π0) (hA3 : A3 M π0) :
    TendstoInDistribution (fun n => lrStat M π0 X ξ0 n) atTop id (fun _ => P)
      (chiSquared (kappa M π0)) := by sorry

end WiesemannRMDP.SRect.Supplement
