-- Prove2me | Theorems.Thm_QueryDepthMIS_claim_3_7
-- name    : QueryDepthMIS.claim_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:40:54.913337+00:00
-- url     : https://prove2.me/theorems/2f8d071f-cc7e-4fc2-b319-d366bea2c5f0
-- title:
--   Claim 3.7 — $\Pr[\mathcal E(P,Q) \mid \pi([\tau])] \le (1-\epsilon)^{L/2-1-2b-h}(1-\beta)^{-L}\prod_{k=2}^{L-1} 1/(e|P_k|)$
-- statement:
--   Let $\alpha \in (0, 0.1)$ and let $\beta, \epsilon \in (0, 0.1)$ be constants for which the conclusion of the two-hop lemma (Lemma 3.3) holds. There is $A_0$ such that for every $A \ge A_0$ the following holds. Let $G$ be a simple graph on $n \ge 2$ vertices, put
--   $$
--   h = \lceil 18 \log n \rceil,\qquad L = \lceil \sqrt{A}\,\log n \rceil,\qquad \tau = \lceil 18 \ln n \rceil,\qquad b = 1 + \lfloor \log_{1+\alpha} n \rfloor,
--   $$
--   let $P = (p_1, \dots, p_L)$ be positions with $A \log n < p_1 < \cdots < p_L < \beta n$, and let $Q \subseteq \{p_1, \dots, p_{L-2}\}$ with $|Q| \le h$. Let $\mathcal B$ be the event $\Delta(G_{\mathrm{alive}}(\tau + 1, n)) \le n/2$, which depends only on the prefix $\pi([\tau])$. Conditioned on any prefix satisfying $\mathcal B$,
--   $$
--   \Pr[\mathcal E(P, Q) \mid \pi([\tau])] \le (1 - \epsilon)^{L/2 - 1 - 2b - h}\,(1 - \beta)^{-L} \prod_{k=2}^{L-1} \frac{1}{e|P_k|},
--   $$
--   where $\mathcal E(P, Q)$ is the event that $P$ is a query path with shortcut set $C(P) = Q$ and $P_k$ are the protected sets of §3.4.
--
--   The bound collects one factor $1/(e|P_k|)$ per edge of the path and a factor $1 - \epsilon$ per application of the two-hop lemma.
--
--   Differences from the source:
--   - reading: A a sufficiently large constant (p.14) and β, ε the constants of Lemma 3.3 → ∀ α ∈ (0, 0.1), ∀ β, ε ∈ (0, 0.1) with TwoHopBound β ε, ∃ A₀, ∀ A ≥ A₀; reason: the paper fixes β, ε by Lemma 3.3 and then takes A large depending on α, β, ε (p.17); any pair satisfying the two-hop conclusion may play the role of Lemma 3.3's pair, which specializes to the paper's
--   - encoding: conditioned on any prefix π([τ]) satisfying B = {Δ(G_alive(τ + 1, n)) ≤ n/2} → for every reference permutation ω₀ satisfying B, condProb given the positions {1, …, τ} of ω₀; reason: B is determined by π([τ]), so every prefix satisfying B is the prefix of such an ω₀
--   - encoding: Pr_T[X | π(S)], the probability when exposing π(T) given π(S) → condProb X S ω₀: the uniform probability of X over all permutations agreeing with a reference ω₀ on the positions in S; reason: X is determined by the positions in S ∪ T, so averaging over all completions equals the paper's probability; ω₀ is arbitrary, i.e. any value of π(S)
--   - encoding: a uniformly random permutation π of V, π(i) the i-th vertex → the uniform (counting) law on orderings ω : V ≃ Fin n, π = ω⁻¹, with 1-based ranks rank ω v = ω v + 1; reason: the same law; positions keep the paper's 1-based values
--   - encoding: a simple graph G with no order on V → an additional instance [LinearOrder V]; reason: required by the reused RGMISFast.tau to break rank ties; ranks of a permutation are injective, so it never acts
--   - encoding: a sequence of positions p₁ < ⋯ < p_L → the list of vertices at those positions, whose ranks are the positions; reason: positions and vertices correspond bijectively under rank
--   - encoding: the standing assumption of §3.1 (p.11), 'we also assume, without loss of generality, that n ≥ n₀ for a sufficiently large constant n₀' → every n ≥ 2; reason: P is nonempty with A log₂ n < p₁ < βn < n, so n > A ≥ A₀; enlarging A₀ to at least n₀ makes the two versions equivalent
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), Claim 3.7, display (3), p.16

import Mathlib
import Definitions.Def_QueryDepthMIS_TwoHopBound
import Definitions.Def_QueryDepthMIS_pathEvent
import Definitions.Def_QueryDepthMIS_prot
import Definitions.Def_QueryDepthMIS_bNum

set_option autoImplicit false

namespace QueryDepthMIS

/-- Claim 3.7 (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…), Claim 3.7, display (3), p.16): "Conditioned on any prefix satisfying B,
Pr[E(P, Q) | π([τ])] ≤ (1 − ϵ)^{L/2−1−2b−h}(1 − β)^{−L} ∏_{k=2}^{L−1} 1/(e|P_k|)."

**Formalization Note** The setting of §3.4 (pp.14–16) with `n = |V| ≥ 2`, `h = ⌈18 log n⌉`,
`L = ⌈√A · log n⌉`, `τ = ⌈18 ln n⌉`, `b = 1 + ⌊log_{1+α} n⌋`, a strictly increasing position
list `P` of length `L` in `(A log n, βn)` and `Q ⊆ {p₁, …, p_{L−2}}` with `|Q| ≤ h`.
"Conditioned on any prefix satisfying B": for every reference permutation `ω₀` satisfying
`B = {Δ(G_alive(τ + 1, n)) ≤ n/2}`, the probability is `condProb` given the positions
`[τ] = {1, …, τ}` of `ω₀`. "The ε, β of Lemma 3.3" are any `β, ε ∈ (0, 0.1)` satisfying its
conclusion `TwoHopBound β ε` (Lemma 3.3 provides such a pair). `A` sufficiently large is read as
`∃ A₀, ∀ A ≥ A₀`, with `A₀` allowed to depend on `α, β, ε`. The exponent `L/2 − 1 − 2b − h` is
real (`Real.rpow`); `(1 − β)^{−L}` is `((1 − β)^L)⁻¹`; `P_k` is `prot α n P k`, `k` 1-based. -/
theorem claim_3_7 :
    ∀ α : ℝ, 0 < α → α < 0.1 →
    ∀ β ε : ℝ, 0 < β → β < 0.1 → 0 < ε → ε < 0.1 → TwoHopBound β ε →
    ∃ A₀ : ℝ, ∀ A : ℝ, A₀ ≤ A →
    ∀ (V : Type) [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
      2 ≤ Fintype.card V →
    ∀ (P : List ℕ), P.length = ⌈Real.sqrt A * Real.logb 2 (Fintype.card V)⌉₊ →
      P.IsChain (· < ·) →
      (∀ p ∈ P, A * Real.logb 2 (Fintype.card V) < (p : ℝ) ∧
        (p : ℝ) < β * (Fintype.card V : ℝ)) →
    ∀ (Q : Finset ℕ), Q ⊆ (P.take (P.length - 2)).toFinset →
      Q.card ≤ ⌈18 * Real.logb 2 (Fintype.card V)⌉₊ →
    ∀ (ω₀ : Perm V),
        (maxDegOn G (aliveSet G (rank ω₀) (⌈18 * Real.log (Fintype.card V)⌉₊ + 1)
          (Fintype.card V)) : ℝ) ≤ (Fintype.card V : ℝ) / 2 →
      condProb (pathEvent G P Q) (Finset.Icc 1 ⌈18 * Real.log (Fintype.card V)⌉₊) ω₀ ≤
        (1 - ε) ^ ((P.length : ℝ) / 2 - 1 - 2 * (bNum α (Fintype.card V) : ℝ) -
            (⌈18 * Real.logb 2 (Fintype.card V)⌉₊ : ℝ)) *
          ((1 - β) ^ P.length)⁻¹ *
          ∏ k ∈ Finset.Icc 2 (P.length - 1),
            1 / (Real.exp 1 * ((prot α (Fintype.card V) P k).card : ℝ)) := by sorry

end QueryDepthMIS
