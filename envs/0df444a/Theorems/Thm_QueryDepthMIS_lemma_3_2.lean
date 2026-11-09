-- Prove2me | Theorems.Thm_QueryDepthMIS_lemma_3_2
-- name    : QueryDepthMIS.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:34:26.458203+00:00
-- url     : https://prove2.me/theorems/bba18c6d-bb7d-4ef2-ac54-8bad8850bdc1
-- title:
--   Lemma 3.2 — one-hop lemma: $\Pr_{P_1\cup\{p_2\}}[F \mid \pi(S)] \le 1/(e\ell(1-\beta))$
-- statement:
--   Let $\beta \in (0, 0.1)$ and let $G$ be a simple graph on $n \ge 2$ vertices. Let $P_1$ be a nonempty set of positions, $\ell = |P_1|$, and $p_1, p_2$ positions with $P_1 < p_1 < p_2 < \beta n$. Suppose that a set of positions $S \subseteq [\beta n]$ is already exposed, and that
--
--   1. (A1) $S$ contains $p_1$ and all positions in $[\max P_1] \setminus P_1$;
--   2. (A2) $S$ contains no position of $P_1 \cup \{p_2\}$;
--   3. (A3) for some integer $1 \le \tau < \min P_1$, $[\tau] \subseteq S$ and $\Delta(G_{\mathrm{alive}}(\tau + 1, n)) \le n/2$.
--
--   Let $F$ be the event that $(\pi(p_1), \pi(p_2)) \in E$ and both vertices are alive at time $\max P_1 + 1$. Then
--   $$
--   \Pr_{P_1 \cup \{p_2\}}[F \mid \pi(S)] \le \frac{1}{e\ell(1 - \beta)} .
--   $$
--   Here $[t] = \{1, \dots, \lfloor t \rfloor\}$ and $P_1 < p_1$ means $\max P_1 < p_1$.
--
--   A vertex that must stay alive while $\ell$ earlier positions are exposed and then gain an alive neighbour pays a factor of order $1/(e\ell)$, independently of the maximum degree; this replaces the $\Delta/n$ factor of the bounded-degree argument.
--
--   Differences from the source:
--   - encoding: a uniformly random permutation π of V, π(i) the i-th vertex → the uniform (counting) law on orderings ω : V ≃ Fin n, π = ω⁻¹, with 1-based ranks rank ω v = ω v + 1; reason: the same law; positions keep the paper's 1-based values
--   - encoding: a simple graph G with no order on V → an additional instance [LinearOrder V]; reason: required by the reused RGMISFast.tau to break rank ties; ranks of a permutation are injective, so it never acts
--   - encoding: Pr_T[X | π(S)], the probability when exposing π(T) given π(S) → condProb X S ω₀: the uniform probability of X over all permutations agreeing with a reference ω₀ on the positions in S; reason: X is determined by the positions in S ∪ T, so averaging over all completions equals the paper's probability; ω₀ is arbitrary, i.e. any value of π(S)
--   - encoding: Δ(G_alive(τ + 1, n)) ≤ n/2 as part of the exposed information → the same inequality evaluated at the reference permutation ω₀; reason: it depends only on the positions [τ] ⊆ S, on which ω₀ and every conditioned permutation agree
--   - generalization: the standing assumption of §3.1 (p.11), 'we also assume, without loss of generality, that n ≥ n₀ for a sufficiently large constant n₀' → every n ≥ 2 (the hypotheses already force n > 40); reason: the proof (pp.19–20) uses no lower bound on n; for n ≥ n₀ the Lean statement is the printed lemma
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), Lemma 3.2, p.12

import Mathlib
import Definitions.Def_QueryDepthMIS_condProb
import Definitions.Def_QueryDepthMIS_aliveSet
import Definitions.Def_QueryDepthMIS_maxDegOn
import Definitions.Def_QueryDepthMIS_oneHopEvent

set_option autoImplicit false

namespace QueryDepthMIS

/-- Lemma 3.2 (The one-hop lemma) (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…), Lemma 3.2, p.12): "For any β ∈ (0, 0.1), the following
holds. Consider a non-empty set of positions P₁ and two positions p₁, p₂ such that
P₁ < p₁ < p₂ < βn. Suppose that a set of positions S ⊆ [βn] is already exposed, and that (A1) S
contains p₁ and all positions in [max P₁] \ P₁, (A2) S does not contain any position in P₁ ∪ {p₂}.
(A3) For some integer 1 ≤ τ < min P₁, we have [τ] ⊆ S and Δ(G_alive(τ + 1, n)) ≤ n/2. Let F be
the event that (π(p₁), π(p₂)) ∈ E and both vertices are alive at time max P₁ + 1. Then
Pr_{P₁∪{p₂}}[F | π(S)] ≤ 1/(eℓ(1 − β)), ℓ = |P₁|."

**Formalization Note** `[t] = {1, …, ⌊t⌋}`, so `S ⊆ [βn]` is `1 ≤ q ≤ βn` for `q ∈ S`.
`Pr_{P₁∪{p₂}}[F | π(S)]` is `condProb (oneHopEvent G P₁ p₁ p₂) S ω₀` for an arbitrary value `ω₀`
of the exposed positions (the event is determined by the positions of `S ∪ P₁ ∪ {p₂}`); the
degree condition of (A3) is evaluated at `ω₀` and depends only on `[τ] ⊆ S`. `max P₁` is
`P₁.sup id`; `P₁ < p₁` means every element of `P₁` is below `p₁`. `n ≥ 2` is the standing
assumption of §2.1. -/
theorem lemma_3_2 :
    ∀ β : ℝ, 0 < β → β < 0.1 →
    ∀ (V : Type) [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
      2 ≤ Fintype.card V →
    ∀ (P₁ : Finset ℕ), P₁.Nonempty →
    ∀ (p₁ p₂ : ℕ), (∀ x ∈ P₁, x < p₁) → p₁ < p₂ → (p₂ : ℝ) < β * (Fintype.card V : ℝ) →
    ∀ (S : Finset ℕ), (∀ q ∈ S, 1 ≤ q ∧ (q : ℝ) ≤ β * (Fintype.card V : ℝ)) →
      p₁ ∈ S → (∀ q, 1 ≤ q → q ≤ P₁.sup id → q ∉ P₁ → q ∈ S) →
      (∀ q ∈ S, q ∉ P₁ ∧ q ≠ p₂) →
    ∀ (τ : ℕ), 1 ≤ τ → (∀ x ∈ P₁, τ < x) → (∀ q, 1 ≤ q → q ≤ τ → q ∈ S) →
    ∀ (ω₀ : Perm V),
      (maxDegOn G (aliveSet G (rank ω₀) (τ + 1) (Fintype.card V)) : ℝ) ≤
        (Fintype.card V : ℝ) / 2 →
      condProb (oneHopEvent G P₁ p₁ p₂) S ω₀ ≤
        1 / (Real.exp 1 * (P₁.card : ℝ) * (1 - β)) := by sorry

end QueryDepthMIS
