-- Prove2me | Theorems.Thm_SmartExpediteAudit_PolicyM_theorem_1_full
-- name    : SmartExpediteAudit.PolicyM.theorem_1_full
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:47:24.393073+00:00
-- url     : https://prove2.me/theorems/07b4cc7f-2ef0-4d8a-9f5d-0bbf5a2e1438
-- title:
--   Theorem 1 — Policy-M state space and continuous-time limiting product law
-- statement:
--   Consider $K\ge1$ single-server nodes, independent Poisson demand of rate $\lambda>0$, and independent exponential services of rates $\mu_1,\ldots,\mu_K>0$. Let $u=(u_{ij})_{0\le i<j\le K}$ be nonnegative extended-integer Policy-M thresholds, nondecreasing in $j$, nonincreasing in $i$, with $u_{iK}=\infty$. Require exactly Assumption A, p. 17:
--
--   $$u_{kj}\le u_{ki}+u_{ij}\quad(0\le k<i<j\le K),\qquad u_{ij}+u_{kl}\le u_{kj}+u_{il}\quad(0\le k<i<j<l\le K).$$
--
--   Write $n[a,b]=\sum_{k=a}^bn_k$ and let $P_t(x,n)$ be the canonical continuous-time transition law computed from the published arrival and enabled-service rates, as defined by the transient-law item. The states reachable from the empty system through positive-rate operational transitions are exactly
--
--   $$S_M(u)=\{n\in\mathbb N^K:n[k+1,l]\le u_{kl}\text{ for all }0\le k<l\le K\}.$$
--
--   Without a stability hypothesis, the auxiliary clock rate is positive, the uniformized kernel and all its powers are stochastic, all series defining the powers and Poisson mixture converge, and $P_t$ is a stochastic semigroup with the identity initial law and the operational right generator. From an admissible state it gives zero mass outside $S_M(u)$.
--
--   If $\lambda<\mu_K$ and $u_{0i}<\infty$ for every $1\le i<K$, then
--
--   $$G(u)=\sum_{n\in S_M(u)}\prod_{k=1}^K(\lambda/\mu_k)^{n_k}\in(0,\infty),\qquad \pi_M(n)=\frac{\mathbf1_{S_M(u)}(n)}{G(u)}\prod_{k=1}^K(\lambda/\mu_k)^{n_k},$$
--   $$\pi_M(n)\ge0,\qquad \sum_{n\in\mathbb N^K}\pi_M(n)=1,\qquad \lim_{t\to\infty}P_t(x,n)=\pi_M(n)\quad(x\in S_M(u),\ n\in\mathbb N^K).$$
--
--   Both clauses of Theorem 1 and the genuine time limit in (8) are retained. Upstream rates may satisfy $\lambda\ge\mu_i$; zero or equal thresholds, $K=1$, empty nodes and the unbounded terminal queue remain included. The result identifies long-run occupancy probabilities for evaluating Policy-M; the existing proved balance-only theorem does not include this time limit.
--
--   Differences from the source:
--   - encoding: One-based nonnegative integer occupancies and thresholds, including infinite terminal thresholds → Fin K to natural occupancies with the published one-based accessor, and extended-natural thresholds; irrelevant threshold entries are unused; reason: This represents exactly the numbered nodes and the infinite entries required on p. 15, including zero and equal thresholds
--   - reading: State-space in (11) and the ergodic time limit (8) with no explicit initial-state subscript → The positive-rate class reachable from the empty state is exactly S_M, and the limit holds from every initial x in S_M; reason: Section 3.4 p. 15 gives the ergodic interpretation; the reachable-class reading fixes initialization without restricting admissible initial states
--   - encoding: Independent Poisson demand and exponential single-node services with Policy-M routing → The canonical Poisson mixture of countable transition powers at clock rate c=2(lambda+sum mu), with stochasticity, convergent series, semigroup, initial identity and right generator asserted as conclusions; reason: Uniformization inserts holding epochs only; the generator is exactly q(x,y) minus the diagonal exit rate, so no event rate or time scale changes
--   - encoding: A normalizing constant G and the product law for states in S_M → G is the convergent countable sum of the exact product powers, is positive and real finite, and pi_M has nonnegative masses summing to one and is zero outside S_M; P_t is also zero there from admissible starts; reason: These are the explicit well-definedness and support clauses implicit in a normalizing constant and probability law; nonsummable tsum defaults and division by zero cannot discharge the goal
--   - generalization: Theorem 1 and (8) describe the process on its admissible state space S_M → The unconditional stochasticity, transition-power convergence, semigroup, initial-law and right-generator certificates hold on all natural occupancy vectors, including starts outside S_M; the limiting-law clause still requires x in S_M; reason: The published operational routing and enabled-event rates are well defined for every natural occupancy vector and their total rate is bounded by lambda+sum mu; restricting these certificates to S_M recovers every source instance without adding a hypothesis
-- source:
--   Song et al., SSRN 3702068, September 28, 2020 version, https://ssrn.com/abstract=3702068, Theorem 1, p. 18, (11)–(12), with (8), p. 15; model pp. 10–17; Appendix A pp. 33–38

import Mathlib
import Definitions.Def_SmartExpediteAudit_PolicyM_Transient

open Filter SmartExpedite.PolicyM
open scoped Topology NNReal

namespace SmartExpediteAudit.PolicyM

/-- Song et al., SSRN 3702068, September 28, 2020 version, Theorem 1,
p. 18, (11) and (12), with the continuous-time meaning (8), p. 15.
The unconditional first part also certifies that the Poisson mixture is a
stochastic semigroup with the operational generator. All summability and
well-posedness assertions are conclusions. Stability is required only for the
normalization and limiting-product-law part. No upstream load restriction,
strict threshold separation, positive threshold or K >= 2 restriction is added. -/
theorem theorem_1_full (K : ℕ) (u : ℕ → ℕ → ℕ∞) (lam : ℝ) (mu : ℕ → ℝ)
    (hK : 1 ≤ K) (hlam : 0 < lam)
    (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k)
    (hu : IsPolicyParam K u) (hA : AssumptionA K u) :
    {n : Fin K → ℕ | Relation.ReflTransGen
      (fun a b => 0 < rate K u lam mu a b) 0 n} = SM K u ∧
    0 < clockRate K lam mu ∧
    MarkovMixing.IsStochasticC (uniformStep K u lam mu) ∧
    (∀ r, MarkovMixing.IsStochasticC
      (MarkovMixing.stepPow (uniformStep K u lam mu) r)) ∧
    (∀ r x n, Summable (fun y : Fin K → ℕ =>
      MarkovMixing.stepPow (uniformStep K u lam mu) r x y *
        uniformStep K u lam mu y n)) ∧
    (∀ t, HasSum (poissonMass K lam mu t) 1) ∧
    (∀ t x n, HasSum (fun r => poissonMass K lam mu t r *
      MarkovMixing.stepPow (uniformStep K u lam mu) r x n)
        (transient K u lam mu t x n)) ∧
    (∀ t, MarkovMixing.IsStochasticC (transient K u lam mu t)) ∧
    (∀ x n, transient K u lam mu 0 x n = if x = n then 1 else 0) ∧
    (∀ s t x n, HasSum (fun y : Fin K → ℕ =>
      transient K u lam mu s x y * transient K u lam mu t y n)
        (transient K u lam mu (s + t) x n)) ∧
    (∀ x n, Tendsto
      (fun t : ℝ≥0 =>
        (transient K u lam mu t x n - (if x = n then 1 else 0)) / (t : ℝ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (rate K u lam mu x n -
        if x = n then outRate K lam mu x else 0))) ∧
    (∀ x ∈ SM K u, ∀ n, n ∉ SM K u →
      ∀ t, transient K u lam mu t x n = 0) ∧
    ((lam < mu K) →
      (∀ i, 1 ≤ i → i < K → u 0 i ≠ ⊤) →
      Summable ((SM K u).indicator (weight K lam mu)) ∧
      0 < normG K u lam mu ∧
      (∀ n, 0 ≤ piM K u lam mu n) ∧
      HasSum (piM K u lam mu) 1 ∧
      (∀ n ∈ SM K u, piM K u lam mu n =
        (∏ k ∈ Finset.Icc 1 K, (lam / mu k) ^ occ n k) / normG K u lam mu) ∧
      (∀ n, n ∉ SM K u → piM K u lam mu n = 0) ∧
      ∀ x ∈ SM K u, ∀ n : Fin K → ℕ,
        Tendsto (fun t : ℝ≥0 => transient K u lam mu t x n)
          atTop (nhds (piM K u lam mu n))) := by sorry

end SmartExpediteAudit.PolicyM
