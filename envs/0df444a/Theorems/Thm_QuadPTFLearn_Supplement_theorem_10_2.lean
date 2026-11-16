-- Prove2me | Theorems.Thm_QuadPTFLearn_Supplement_theorem_10_2
-- name    : QuadPTFLearn.Supplement.theorem_10_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:43:45.368386+00:00
-- url     : https://prove2.me/theorems/8b5a80fd-f482-400d-a459-4efc53497a5a
-- title:
--   Theorem 10.2, p.93 — SQ lower bound: tolerance $d^{-\Omega(k)}$ or $2^{d^{\Omega(1)}}$ queries to learn $\mathcal H_k$ to error below $1/2$
-- statement:
--   **SQ lower bound.** There are universal constants $c,c_0>0$ with the following property. Let $k\ge1$ be an integer and $\gamma\in(0,1/2)$ a constant, and let $d$ be sufficiently large depending on $k$ and $\gamma$. Consider any statistical query algorithm on $\mathbb R^d$ (Definition 10.1) that
--
--   1. uses only queries of tolerance greater than $d^{-ck}$, and
--   2. always stops after fewer than $2^{d^{c_0}}$ queries.
--
--   Then the algorithm does not learn intersections of $k$ degree-2 PTFs under the Gaussian distribution to error $1/2-\gamma$. Concretely, there are polynomials $q_1,\dots,q_k$ of degree at most two, with target $f(x)=1\{q_1(x)\ge0,\dots,q_k(x)\ge0\}$, and an oracle $\mathrm{STAT}_{D_q}$ valid for the law $D_q$ of $(x,2f(x)-1)$, $x\sim N(0,I_d)$, such that
--   $$\Pr_{\text{coins}}\Bigl[\text{the output } h \text{ satisfies } \Pr_{x\sim N(0,I_d)}[h(x)\ne 2f(x)-1]\le\tfrac12-\gamma\Bigr]<\tfrac23 .$$
--   Equivalently, any SQ algorithm that learns $\mathcal H_k$ to any constant error below $1/2$ with probability $2/3$ must either use a query of tolerance at most $d^{-\Omega(k)}$ or make at least $2^{d^{\Omega(1)}}$ queries.
--
--   The theorem shows that the $d^{O(k)}$ dependence of the paper's learner (Theorem 1.3) is essentially necessary for SQ algorithms. In this respect intersections of quadratic PTFs differ from intersections of halfspaces, which SQ algorithms learn with a universal exponent of $d$.
--
--   **Formalization Note** The SQ model is `QuadPTFLearn.Supplement.SQ`. Queries must be legal (measurable, values in $[-1,1]$, positive tolerance) and outputs measurable. Both restrictions, and the query budget, are required on every history of the strategy. The oracle is memoryless, and the success probability is the outer measure of the success set under the coin law.
--
--   Differences from the source:
--   - reading: Let k ∈ ℤ₊ and let d ∈ ℤ₊ be sufficiently large depending on k … to any constant error smaller than 1/2 … d^{−Ω(k)} … 2^{d^{Ω(1)}} → ∃ c, c₀ > 0 ∀ k ≥ 1 ∀ γ ∈ (0, 1/2) ∃ d₀ ∀ d ≥ d₀: tolerance threshold d^{−ck}, query threshold 2^{d^{c₀}}; reason: Theorem 1.5 (p.3) says d is sufficiently large as a function of k and γ for a fixed constant γ ∈ (0, 1/2), and the proof (p.96) takes 'universal constants c, c₀ > 0'; constants independent of k and γ are the stronger reading
--   - reading: any SQ algorithm that learns … (success probability unstated) → success means error ≤ 1/2 − γ with probability at least 2/3 over the algorithm's coins; reason: Theorem 1.5 and the proof (p.96) both say 'with success probability at least 2/3'
--   - encoding: must either (i) use a query with tolerance at most d^{−Ω(k)}, or (ii) make at least 2^{d^{Ω(1)}} queries → if every query the strategy can ask (any coins, any answer list) is legal with tolerance > d^{−ck}, and against every oracle and every coin outcome the run stops after fewer than 2^{d^{c₀}} queries, then it fails for some target and some valid oracle; reason: the contrapositive; restricting the strategy on every history rather than on reachable ones is equivalent, because a strategy can be truncated off its reachable histories (stopping instead) without changing any run against a valid oracle
--   - generalization: for every sequence of responses satisfying the tolerance bounds (Definition 10.1): the learner fails against some admissible responses → there is a memoryless oracle O (a function of the query) valid for D_q on every legal query, against which the learner fails; reason: a memoryless valid oracle produces a response sequence satisfying the tolerance bounds, so exhibiting one is a stronger conclusion that specializes to the source's
--   - generalization: probability (over the algorithm's randomness) of the success event → outer measure, under the coin law μ, of the set of coin outcomes whose run outputs h with error ≤ 1/2 − γ; reason: the success set need not be measurable; outer measure < 2/3 bounds the measure of every measurable subset, so the claim specializes to the source's
--   - generalization: the learner outputs a hypothesis h with {±1} values → the output h : ℝᵈ → ℝ is any measurable function, and its error is Pr_{x∼N(0,I)}[h(x) ≠ 2f(x) − 1]; reason: the lower bound then covers more algorithms; a {±1}-valued output is a particular case
--   - encoding: a hypothesis h with error Pr_{(x,y)∼D}[h(x) ≠ y] (Definition 1.2) → outputs are measurable functions; reason: err_D(h) is a probability, which Definition 1.2 presupposes; the paper's own reduction queries 1{h(x) ≠ y}
--   - encoding: query functions ϕ : ℝᵈ × {±1} → [−1, 1], tolerance τ > 0; an SQ algorithm that may choose each query and tolerance adaptively → measurable φ : ℝᵈ × ℝ → ℝ with |φ| ≤ 1, τ > 0; a probability space of coins of arbitrary type and a strategy from (coins, answers so far) to the next query or a hypothesis; reason: every query on ℝᵈ × {±1} extends to such a φ and only its values at ±1 matter; measurability makes E_D[ϕ] defined; arbitrary coins cover every randomized algorithm
--   - encoding: intersections of k degree-2 PTFs with Gaussian marginals (Definition 1.2), {±1} labels (§10) → targets ptfInd q with q : Fin k → Poly d, deg q_i ≤ 2, and the law D_q of (x, 2·ptfInd q x − 1), x ∼ N(0, I_d); reason: Definition 1.2's realizable laws, written with §10's label convention
-- source:
--   Diakonikolas, Kane, Ma, Ren, Tran, Beyond Multi-Index Models: Learning Intersections of Degree-2 PTFs, arXiv:2611.05114 (sha256 4d6ea892…), Theorem 10.2, p.93 (PDF p.95); Definition 10.1, p.93; Theorem 1.5, p.3 (PDF p.5); proof, p.96 (PDF p.98)

import Mathlib
import Definitions.Def_QuadPTFLearn_Supplement_SQ

open MeasureTheory ProbabilityTheory

namespace QuadPTFLearn

namespace Supplement

/-- I. Diakonikolas, D. M. Kane, M. Ma, L. Ren, T. Tran, *Beyond Multi-Index Models: Learning
Intersections of Degree-2 PTFs*, arXiv:2611.05114 (held copy, sha256 4d6ea892…5aed).
Theorem 10.2, p.93 (PDF p.95), with Definition 10.1, p.93, its informal restatement Theorem 1.5,
p.3 (PDF p.5), and the proof, p.96 (PDF p.98).

There are universal constants `c, c₀ > 0` such that for every `k ≥ 1` and every constant
`γ ∈ (0, 1/2)`, for all sufficiently large `d` (depending on `k` and `γ`): every SQ algorithm on
`ℝᵈ` whose queries are all legal with tolerance greater than `d^{−ck}`, whose outputs are
measurable, and which always stops after fewer than `2^{d^{c₀}}` queries, fails for some target:
there are an intersection `f = 1{q₁ ≥ 0, …, q_k ≥ 0}` of `k` polynomials of degree at most two and
an oracle valid for the law of `(x, 2f(x) − 1)`, `x ∼ N(0, I_d)`, against which the probability
(over the algorithm's coins) of outputting `h` with `Pr_{x∼N(0,I)}[h(x) ≠ 2f(x) − 1] ≤ 1/2 − γ`
is less than `2/3`.

**Formalization Note.** Contrapositive form of "must either (i) use a query with tolerance at most
`d^{−Ω(k)}`, or (ii) make at least `2^{d^{Ω(1)}}` queries", with the success probability `2/3`
of Theorem 1.5 and of the proof. The restrictions on the algorithm quantify over every coin
outcome and every answer list (an algorithm can be changed off its reachable histories without
changing any run). The query count is bounded against every oracle. The oracle is memoryless
(a function of the query). The probability of success is the outer measure of the success set
under the coin law. Labels are `±1` (§10's convention); `lawPM q` is Definition 1.2's
realizable law with `{±1}` labels. -/
theorem theorem_10_2 :
    ∃ c c₀ : ℝ, 0 < c ∧ 0 < c₀ ∧
      ∀ k : ℕ, 1 ≤ k → ∀ γ : ℝ, 0 < γ → γ < 1 / 2 →
      ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∀ A : SQAlg d,
        (∀ ω as Q, A.next ω as = Sum.inl Q →
          Q.Legal ∧ (d : ℝ) ^ (-(c * k)) < Q.tol) →
        (∀ ω as h, A.next ω as = Sum.inr h → Measurable h) →
        (∀ (O : SQOracle d) ω, ∃ n : ℕ, (n : ℝ) < 2 ^ ((d : ℝ) ^ c₀) ∧
          ∃ h, StopsWith A O ω n h) →
        ∃ q : Fin k → Poly d, IsQuadFamily q ∧ ∃ O : SQOracle d, ValidOracle (lawPM q) O ∧
          A.μ {ω | ∃ n h, StopsWith A O ω n h ∧
            gauss d {x | h x ≠ 2 * ptfInd q x - 1} ≤ ENNReal.ofReal (1 / 2 - γ)} < 2 / 3 := by sorry

end Supplement

end QuadPTFLearn
