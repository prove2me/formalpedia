-- Prove2me | Theorems.Thm_QueryDepthMIS_lemma_3_3
-- name    : QueryDepthMIS.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:36:37.03721+00:00
-- url     : https://prove2.me/theorems/9aa2c07e-48bb-42cf-b9cc-f2687f9523c2
-- title:
--   Lemma 3.3 — two-hop lemma: $\Pr[\mathcal G \mid \pi(S)] \le (1-\epsilon)/(e\ell)^2$
-- statement:
--   There exist constants $\beta \in (0, 0.1)$ and $\epsilon \in (0, 0.1)$ such that the following holds for every simple graph $G$ on $n \ge 2$ vertices. Consider two sets of positions $P_1, P_2$ with $|P_1| = |P_2| = \ell$ for some $\ell > 10^3$, and three positions $p_1, p_2, p_3$ with
--   $$
--   P_1 < P_2 < p_1 < p_2 < p_3 < \beta n .
--   $$
--   Suppose that a set of positions $S \subseteq [\beta n]$ is already exposed, and that
--
--   1. $S$ contains $p_1$ and all positions in $[\max P_2] \setminus P_1 \setminus P_2$;
--   2. $S$ contains no position of $P_1 \cup P_2 \cup \{p_2, p_3\}$;
--   3. for some integer $1 \le \tau < \min P_1$, $[\tau] \subseteq S$ and $\Delta(G_{\mathrm{alive}}(\tau + 1, n)) \le n/2$.
--
--   Let $\mathcal G$ be the event that $(p_1, p_2, p_3)$ forms an induced path, $p_1$ is alive at time $\max P_1 + 1$, and $p_2, p_3$ are alive at time $\max P_2 + 1$. Then
--   $$
--   \Pr_{P_1 \cup P_2 \cup \{p_2, p_3\}}[\mathcal G \mid \pi(S)] \le \frac{1 - \epsilon}{(e\ell)^2}.
--   $$
--
--   Two consecutive one-hop events along an induced path cannot both attain the one-hop bound; the gain of $1 - \epsilon$ per pair is what makes the final union bound converge.
--
--   **Formalization Note** The conclusion for given $\beta, \epsilon$ is the definition `TwoHopBound β ε`; the constants are chosen before the graph.
--
--   Differences from the source:
--   - encoding: a uniformly random permutation π of V, π(i) the i-th vertex → the uniform (counting) law on orderings ω : V ≃ Fin n, π = ω⁻¹, with 1-based ranks rank ω v = ω v + 1; reason: the same law; positions keep the paper's 1-based values
--   - encoding: a simple graph G with no order on V → an additional instance [LinearOrder V]; reason: required by the reused RGMISFast.tau to break rank ties; ranks of a permutation are injective, so it never acts
--   - encoding: Pr_T[X | π(S)], the probability when exposing π(T) given π(S) → condProb X S ω₀: the uniform probability of X over all permutations agreeing with a reference ω₀ on the positions in S; reason: X is determined by the positions in S ∪ T, so averaging over all completions equals the paper's probability; ω₀ is arbitrary, i.e. any value of π(S)
--   - encoding: Δ(G_alive(τ + 1, n)) ≤ n/2 as part of the exposed information → the same inequality evaluated at the reference permutation ω₀; reason: it depends only on the positions [τ] ⊆ S, on which ω₀ and every conditioned permutation agree
--   - encoding: the standing assumption of §3.1 (p.11), 'we also assume, without loss of generality, that n ≥ n₀ for a sufficiently large constant n₀' → every n ≥ 2 inside TwoHopBound β ε; reason: the hypotheses force βn > p₃ > 2ℓ > 2000; TwoHopBound is antitone in β, so a pair (β, ε) valid for n ≥ n₀ yields the pair (min(β, 2000/n₀), ε) valid for every n, and the two existential statements are equivalent
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), Lemma 3.3, pp.12–13

import Mathlib
import Definitions.Def_QueryDepthMIS_TwoHopBound

set_option autoImplicit false

namespace QueryDepthMIS

/-- Lemma 3.3 (The two-hop lemma) (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…), Lemma 3.3, pp.12–13): "There exist constants
β ∈ (0, 0.1) and ϵ ∈ (0, 0.1) such that the following holds. Consider two sets of positions P₁, P₂
and three positions p₁, p₂, p₃ such that P₁ < P₂ < p₁ < p₂ < p₃ < βn, and |P₁| = |P₂| = ℓ for some
ℓ > 10³. Suppose that a set of positions S ⊆ [βn] is already exposed, and that • S contains p₁ and
all positions in [max P₂] \ P₁ \ P₂, and • S does not contain any position in P₁ ∪ P₂ ∪ {p₂, p₃}.
• For some integer 1 ≤ τ < min P₁, we have [τ] ⊆ S and Δ(G_alive(τ + 1, n)) ≤ n/2. Define the
event G as the intersection of the following: • (p₁, p₂, p₃) forms an induced path, • p₁ is alive
at time max P₁ + 1, and • p₂ and p₃ are alive at time max P₂ + 1. Then,
Pr_{P₁∪P₂∪{p₂,p₃}}[G | π(S)] ≤ (1 − ϵ)/(eℓ)²."

**Formalization Note** The constants `β, ε` are chosen before the graph and everything else;
`TwoHopBound β ε` is the conclusion for all graphs and configurations (see its definition). -/
theorem lemma_3_3 :
    ∃ β ε : ℝ, 0 < β ∧ β < 0.1 ∧ 0 < ε ∧ ε < 0.1 ∧ TwoHopBound β ε := by sorry

end QueryDepthMIS
