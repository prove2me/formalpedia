-- Prove2me | Theorems.Thm_StrictCompatLB_FullInhomogeneous_theorem_3_6_full
-- name    : StrictCompatLB.FullInhomogeneous.theorem_3_6_full
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:39:07.638578+00:00
-- url     : https://prove2.me/theorems/9a4ecffb-ad8d-4fa1-87f4-ed0a80eab452
-- title:
--   Theorem 3.6 — full quenched JSQ(d) limits (corrected: fixed point, finite-prefix claims, and subcriticality definition)
-- statement:
--   Fix $d\ge2$ and $0\le\lambda<1$. At size $N\ge1$ let there be $N$ servers and $M(N)\ge1$ dispatchers. For $p_w(N)\in(0,1]$ put $\bar p(N)=\min_w p_w(N)$ and $A(N)=\sum_w p_w(N)^{-2}$. Assume exactly
--
--   $$
--   \frac{N\bar p(N)}{\log M(N)+\log N}\to\infty,\qquad
--   M(N)\bar p(N)\to\infty,\qquad
--   \frac{\log N}{M(N)^2}A(N)\to0.
--   $$
--
--   Let $P_0$ be any probability law on graph samples whose size-$N$ marginal has independent Bernoulli edges with probability $p_w(N)$ for edge $(v,w)$. Graphs of different sizes need not be independent. For $P_0$-almost every sample, the following statements all concern the fixed sampled environment $G$.
--
--   The graph sequence is proportionally sparse and satisfies the repaired subcriticality condition. There is $N_0\ge1$ such that every original graph $G_N$ for $N\ge N_0$ is connected. On that tail the published uniform-subset JSQ(d) kernel is stochastic, and every initial probability law on $\mathbb N^N$ has an operational realization. Independent dispatcher arrivals have rate $\lambda N/M(N)$, service requirements have mean-one exponential laws, and queues are unbounded. The operational realization is the uniformized tagged chain with an independent clock of rate $(\lambda+1)N$.
--
--   For every $q^0\in\mathcal Y$, there is a unique continuous $\mathcal Y$-valued trajectory starting at $q^0$ and satisfying, with right derivatives at zero,
--
--   $$
--   \dot q_i(t)=\lambda(q_{i-1}(t)^d-q_i(t)^d)-(q_i(t)-q_{i+1}(t)),\quad i\ge1,\qquad q_0(t)=1.
--   $$
--
--   For every sequence of operational laws $P_N^G$ on that tail with initial occupancies converging in probability in $\ell_1$ to $q^0$, and for every finite $T\ge0$ and $\varepsilon>0$,
--
--   $$
--   P_N^G\left(\sup_{0\le t\le T}\|q(\Phi(G_N,t))-q(t)\|_1\ge\varepsilon\right)\to0.
--   $$
--
--   This is the equivalent uniform-in-time form of weak Skorohod-J1 convergence to the deterministic continuous trajectory. The initial laws may be random, have unbounded queues, and lack uniform moment bounds. The limiting state may have infinite support. Arbitrary auxiliary measures or vectors at omitted finite indices do not affect any limit.
--
--   For each $N\ge N_0$ there is a unique stationary probability vector $\pi_N$ of the tagged kernel, and its continuous-time tagged law converges in total variation to $\pi_N$ from every finite configuration. For every choice of these stationary laws and every $\varepsilon>0$, independently of initial configurations,
--
--   $$
--   \pi_N\left(\|q-q^*(\infty)\|_1\ge\varepsilon\right)\to0,\qquad
--   q_0^*(\infty)=1,\quad q_i^*(\infty)=\lambda^{\sum_{k=0}^{i-1}d^k}\quad(i\ge1).
--   $$
--
--   The result retains the queueing consequences of Theorem 3.6 in addition to its already proved graph portion. It supplies existence and uniqueness conclusions rather than assuming a trajectory or stationary law. At zero load the stationary positive-level occupancy is zero. The graph probability-one event is chosen before the universally quantified queueing initial laws.
--
--   Differences from the source:
--   - correction: The printed fixed point (3.4) has exponent (d^i-d)/(d-1) → The exponent is 1+d+...+d^(i-1)=(d^i-1)/(d-1); reason: For lambda=1/2, d=2 and complete graphs, the printed first two coordinates are 1 and 1/4, giving drift -3/4 at level one; stationary flow balance instead gives E[q_1]=1/2
--   - correction: Theorem 3.4 asserts ergodicity for each fixed N under asymptotic subcriticality → Ergodicity holds for every N above a graph-dependent threshold; reason: With M(N)=N, lambda=4/5, d=2, complete graphs except at N=6, five dispatchers at N=6 connected only to servers {1,2} inject rate 4 into capacity 2; the sixth connects to all six. Choosing all p_w(6)=1/2 and p_w(N)=1 otherwise satisfies (3.5) and gives this graph probability 2^-36. Theorem 4.8(i) states the eventual quantifier
--   - correction: The connected-graph standing assumption is stated at every size → The original Bernoulli graphs are eventually connected; process laws and finite-size stability concern that original tail; reason: The same probability sequence gives an empty G_6 with probability 2^-36 despite all three growth limits; no conditioning or change of graph law is permitted
--   - correction: Definition 3.3 asks for a probability vector on every U, including the empty set → The reused subcriticality predicate requires probability normalization only on nonempty U and zero weights off support; reason: No probability distribution exists on U=empty, including for a complete graph satisfying every other assumption
--   - correction: Equation (3.2) divides by choose(degree,d) even when the actual sample size is min(d,degree) → The reused predicate divides by choose(degree,min(d,degree)); reason: At N=1 with one dispatcher, d=2 and its edge present, the sampled singleton is well defined but choose(1,2)=0; on the eventually degree-at-least-d tail the corrected and printed normalizers coincide
--   - reading: Section 2 does not specify replacement in sampling d servers → The finite model samples uniform subsets and uses uniform shortest-queue ties; reason: Definition 3.3 p. 11 and (H.5) p. 47 explicitly sample subsets; the power expression in (3.3) is the limiting formula, not a finite-N hypergeometric identity
--   - reading: Theorem 3.4 writes initial ell-one convergence without specifying the mode → All initial probability laws converging in probability in ell-one are allowed; reason: The probability estimates (F.2) and (F.3) on p. 42 treat the starting state as random; deterministic configurations are included and no moment or tail hypothesis is added
--   - encoding: Sizes and occupancy levels start at N=1 and i=1 → Fin N servers, Fin(M N) dispatchers, an irrelevant N=0 extension with M(0)>0 and 0<p_w(0)<=1, and coordinate q_0=1; reason: Every source sequence admits this extension, every claim concerns the N>=1 tail, and the appended coordinate contributes zero to every occupancy distance
--   - encoding: The process is specified by independent Poisson arrivals, exponential services, and subset routing → The published JSQ kernel is run on the canonical chain-and-clock sample space, with arbitrary initial probability vector and independent exponential gaps of rate (lambda+1)N; reason: Appendix H p. 46 uses this exact uniformization; dummy service events at empty queues preserve the law; existence for every initial law is a conclusion, not a hypothesis
--   - encoding: Weak Skorohod-J1 process convergence to a unique continuous Y-valued solution → Uniform-in-time ell-one convergence in probability to the uniquely existing nonnegative-time trajectory; sums and suprema are in ENNReal; reason: For cadlag paths and a deterministic continuous limit, J1 convergence and uniform convergence agree at the limit, and weak convergence to a constant is convergence in probability; no coordinate truncation or finite-support assumption occurs
--   - encoding: Ergodicity and weak stationary occupancy convergence → A unique stationary probability vector, total-variation attraction from every finite state under every operational law, and stationary ell-one concentration at the fixed point; reason: This is the countable-state ergodic conclusion with its attraction clause made explicit; concentration at a deterministic point is equivalent to weak convergence. At lambda=0 the empty state is absorbing and all positive-level limiting occupancies are zero
-- source:
--   Rutten & Mukherjee, Load Balancing Under Strict Compatibility Constraints, arXiv:2008.07562v2, https://arxiv.org/abs/2008.07562v2, Theorem 3.6 (3.5), PDF p. 14 = printed p. 14; full consequences of Theorem 3.4, (3.3)–(3.4), PDF p. 12 = printed p. 12; standing model §2 pp. 8–9; Defs. 3.1 and 3.3 pp. 10–11; §3.2 p. 13; Theorem 4.8(i) p. 20; (F.2) p. 42; (H.5) p. 47.

import Mathlib
import Definitions.Def_StrictCompatLB_Inhomogeneous_RandomGraph
import Definitions.Def_StrictCompatLB_MeanField_Model
import Definitions.Def_StrictCompatLB_FullInhomogeneous_UniformizedLaw
import Definitions.Def_StrictCompatLB_FullInhomogeneous_Trajectory

open MeasureTheory Filter Topology
open StrictCompatLB.MeanField StrictCompatLB.Inhomogeneous
open scoped ENNReal NNReal

namespace StrictCompatLB.FullInhomogeneous

/-- Complete Theorem 3.6, arXiv:2008.07562v2 p. 14, including every consequence of
Theorem 3.4 p. 12. Corrected: fixed point exponent d^i-1; eventual finite-size claims;
nonempty sampled-set weights and actual binomial normalization in subcriticality.
The finite model uses uniform subsets, as p. 11 and (H.5) prescribe.
The graph law is arbitrary across N; the event is chosen before all queueing initial laws.
Every initial law has an operational realization on the valid original graph tail.
Locally uniform ell-one convergence in probability is the equivalent form of weak J1
convergence to the deterministic continuous solution. Arbitrary finite prefixes are ignored. -/
theorem theorem_3_6_full (d : ℕ) (hd : 2 ≤ d)
    (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (M : ℕ → ℕ) (hM : ∀ N, 0 < M N)
    (p : (N : ℕ) → Fin (M N) → ℝ)
    (hp_pos : ∀ N w, 0 < p N w) (hp_le : ∀ N w, p N w ≤ 1)
    (h1 : Tendsto (fun N : ℕ =>
      (N : ℝ) / (Real.log (M N) + Real.log N) * minEdgeProb M p N) atTop atTop)
    (h2 : Tendsto (fun N : ℕ => (M N : ℝ) * minEdgeProb M p N) atTop atTop)
    (h3 : Tendsto (fun N : ℕ =>
      Real.log N / (M N : ℝ) ^ 2 * ∑ w : Fin (M N), 1 / (p N w) ^ 2) atTop (𝓝 0))
    {Ω : Type*} [MeasurableSpace Ω] (P₀ : Measure Ω) [IsProbabilityMeasure P₀]
    (X : (N : ℕ) → Ω → (Fin N × Fin (M N) → Bool))
    (hX_meas : ∀ N, Measurable (X N))
    (hX_law : ∀ N, P₀.map (X N) = edgeLaw M p N) :
    ∀ᵐ ω ∂P₀,
      let G := fun N => graphOf (X N ω)
      IsPropSparse M G ∧ IsSubcritical d M G ∧
      ∃ N₀ : ℕ, 1 ≤ N₀ ∧
        (∀ N ≥ N₀,
          (compatGraph M G N).Connected ∧
          IsStochasticKernel (jsqdKernel lam d M G N) ∧
          (∀ μ : (Fin N → ℕ) → ℝ, IsProbVec μ →
            ∃ P : Measure (ChainSample (Fin N → ℕ)),
              IsUniformizedLaw P (jsqdKernel lam d M G N) ((lam + 1) * (N : ℝ)) μ) ∧
          (∃ π : (Fin N → ℕ) → ℝ,
            IsStationary (jsqdKernel lam d M G N) π ∧
            (∀ π', IsStationary (jsqdKernel lam d M G N) π' → π' = π) ∧
            AttractsAllStates (jsqdKernel lam d M G N) ((lam + 1) * (N : ℝ)) π)) ∧
        (∀ q₀ : ℕ → ℝ, InY q₀ →
          ∃ s : ℝ≥0 → ℕ → ℝ,
            IsSolution lam d q₀ s ∧
            (∀ s', IsSolution lam d q₀ s' → s' = s) ∧
            ∀ (μ : (N : ℕ) → (Fin N → ℕ) → ℝ)
              (P : (N : ℕ) → Measure (ChainSample (Fin N → ℕ))),
              (∀ N ≥ N₀,
                IsUniformizedLaw (P N) (jsqdKernel lam d M G N) ((lam + 1) * (N : ℝ)) (μ N)) →
              (∀ ε : ℝ, 0 < ε →
                Tendsto (fun N => probOf (μ N)
                  {z | ENNReal.ofReal ε ≤ PowerOfDUniversality.Fluid.l1dist (occ z) q₀})
                  atTop (𝓝 0)) →
              ∀ T : ℝ, 0 ≤ T → ∀ ε : ℝ, 0 < ε →
                Tendsto (fun N => P N {a | ENNReal.ofReal ε ≤
                  PowerOfDUniversality.Fluid.supDistL1
                    (fun t => occ (taggedState a t)) (fun t => s (Real.toNNReal t)) T})
                  atTop (𝓝 0)) ∧
        (∀ π : (N : ℕ) → (Fin N → ℕ) → ℝ,
          (∀ N ≥ N₀, IsStationary (jsqdKernel lam d M G N) (π N)) →
          ∀ ε : ℝ, 0 < ε →
            Tendsto (fun N => probOf (π N)
              {z | ENNReal.ofReal ε ≤ PowerOfDUniversality.Fluid.l1dist
                (occ z) (PowerTwoChoices.Limit.fixedPoint lam d)}) atTop (𝓝 0)) := by sorry

end StrictCompatLB.FullInhomogeneous
