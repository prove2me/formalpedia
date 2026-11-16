-- Prove2me | Theorems.Thm_SymNormLoad_Supplement_theorem_4_1
-- name    : SymNormLoad.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:56:49.241238+00:00
-- url     : https://prove2.me/theorems/0aec9d5c-6ad9-4ee7-b2c8-fe76fec5b215
-- title:
--   Theorem 4.1 — every randomized online algorithm on related machines has ratio $\Omega((\log M/\log\log M)^{\log_4(3/2)})$ for some symmetric norm
-- statement:
--   Consider online load balancing on $M$ related machines: machine $i$ has a positive speed $v_i$, job $j$ has a positive size $p_j$ and takes time $p_j/v_i$ on machine $i$, jobs arrive one at a time and are assigned irrevocably, and the cost of an assignment is $\Psi(L)$ for a monotone symmetric norm $\Psi$ of the load vector $L$, fixed and known in advance. Let
--   $$
--   \alpha=\log_4\tfrac32\approx 0.2925 .
--   $$
--
--   **Theorem.** There is an absolute constant $c>0$ with the following property. For arbitrarily large $M$ (precisely: for every $N_0$ there is $M\ge\max\{N_0,16\}$) there exist speeds $v_1,\dots,v_M>0$ and a monotone symmetric norm $\Psi$ on $\mathbb R^M$ such that every randomized online algorithm that is $\rho$-competitive, in expectation on every fixed input against the offline optimum, satisfies
--   $$
--   \rho\;\ge\;c\left(\frac{\ln M}{\ln\ln M}\right)^{\alpha}.
--   $$
--
--   The bound tends to infinity with $M$, so no online algorithm, even randomized against an oblivious adversary, achieves a constant competitive ratio for every symmetric norm on related machines; constant ratios are known only for the $\ell_q$ norms. The constant $c$ does not depend on $M$, the speeds, the norm or the algorithm, and the algorithm may depend on the speeds and on $\Psi$.
--
--   **Formalization Note** A randomized online algorithm is a probability space $(\Omega,\mu)$, $\Omega$ arbitrary, with a family of deterministic prefix rules $A_\omega$ (the published `OnlineAlgorithm`), required to be measurable in $\omega$ on each input with positive sizes so that its expected cost is defined. "Competitive ratio at least $X$" is "every $\rho$ for which the algorithm is $\rho$-competitive satisfies $X\le\rho$" (so an algorithm with no finite ratio satisfies it trivially). The requirement $M\ge16$ makes $\ln\ln M>0$, so the real power is the honest one. Natural logarithms are used; another base changes only $c$.
--
--   Differences from the source:
--
--   - reading: Ω((log M/ log log M)^α) for arbitrarily large M → ∃ c > 0, ∀ N₀, ∃ M with N₀ ≤ M and 16 ≤ M, and a bound c·(ln M / ln ln M)^α with natural logarithms; reason: the asymptotic clause is informal; this is the standard reading with c absolute (chosen before M, the speeds, the norm and the algorithm), and M ≥ 16 only excludes the M where ln ln M ≤ 0 and the bound is undefined
--   - encoding: the algorithm has competitive ratio at least X → every ρ for which the algorithm is ρ-competitive satisfies X ≤ ρ; reason: the competitive ratio is the infimum of such ρ; same content
--   - encoding: OPT = min over integral assignments σ of Ψ(L_σ) → E[Ψ(L_A)] ≤ ρ·Ψ(L_σ) for every σ; reason: finitely many σ, so the two are equivalent
--   - encoding: a randomized online algorithm (coins independent of the input) → a probability space (Ω : Type, μ) with a family A : Ω → OnlineAlgorithm M, measurable in ω on each input with positive sizes; reason: every distribution over deterministic online rules is of this form; measurability only excludes algorithms whose expected cost is undefined
--   - encoding: Ψ a monotone symmetric norm, machines and jobs 1-based → a plain function on Fin M → ℝ with the published IsMonotoneSymmetricNorm axioms, 0-based indices; reason: the base mission's published convention; same instances
--   - generalization: competitiveness over all job sequences of the related-machine model → competitiveness required only on sequences of positive sizes; reason: fewer inputs make the competitiveness hypothesis weaker, so the bound covers more algorithms and implies the source's (the paper's construction uses positive sizes B^(t−4b_t) only)
-- source:
--   Chen–Im–Sirri, Online Load Balancing under Symmetric Norms, manuscript (STOC 2027 submission), Theorem 4.1, p.24 (proof p.38, Lemmas 4.2–4.7, pp.27–37); model §1.1 and footnote 1, p.2

import Mathlib
import Definitions.Def_SymNormLoad_IsMonotoneSymmetricNorm
import Definitions.Def_SymNormLoad_loadVec
import Definitions.Def_SymNormLoad_OnlineAlgorithm
import Definitions.Def_SymNormLoad_Supplement_relatedTimes
import Definitions.Def_SymNormLoad_Supplement_IsRandCompetitiveRelated

open MeasureTheory

namespace SymNormLoad.Supplement

/-- **Theorem 4.1 (randomized lower bound on related machines).** Chen–Im–Sirri, *Online Load
Balancing under Symmetric Norms*, manuscript (STOC 2027 submission), Theorem 4.1, p.24 (proof
p.38, with Lemmas 4.2–4.7, pp.27–37): for arbitrarily large `M`, there exist `M` related machines
and a monotone symmetric norm `Ψ` such that every randomized online algorithm has competitive
ratio at least `Ω((log M / log log M)^α)` for minimizing `Ψ` of the machine loads, where
`α = log₄(3/2) ≈ 0.2925`.

**Formalization Note** `Ω(·)` is read with one absolute constant `c > 0` chosen before `M`;
"arbitrarily large `M`" is "for every `N₀` there is `M ≥ N₀`" (with `M ≥ 16`, so that
`log log M > 0` and the real power is the honest one). The speeds `v` are positive and `Ψ` is a
plain function with the published `IsMonotoneSymmetricNorm` axioms; both are fixed before the
algorithm. A randomized algorithm is an arbitrary probability space `(Ω, μ)` with a family
`A : Ω → OnlineAlgorithm M` of deterministic prefix rules, measurable in `ω` on every input with
positive sizes (so the expected cost is defined). "Competitive ratio at least `X`" is "every `ρ`
for which the algorithm is `ρ`-competitive satisfies `X ≤ ρ`". Logarithms are natural; `α` is
`Real.logb 4 (3/2)` exactly. -/
theorem theorem_4_1 :
    ∃ c : ℝ, 0 < c ∧ ∀ N₀ : ℕ, ∃ M : ℕ, N₀ ≤ M ∧ 16 ≤ M ∧
      ∃ v : Fin M → ℝ, (∀ i, 0 < v i) ∧
      ∃ Ψ : (Fin M → ℝ) → ℝ, IsMonotoneSymmetricNorm Ψ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (A : Ω → OnlineAlgorithm M),
        (∀ (N : ℕ) (s : Fin N → ℝ), (∀ j, 0 < s j) →
          Measurable (fun ω => runAssign (A ω) (relatedTimes v s))) →
        ∀ ρ : ℝ, IsRandCompetitiveRelated Ψ v μ A ρ →
          c * (Real.log M / Real.log (Real.log M)) ^ Real.logb 4 (3 / 2) ≤ ρ := by sorry

end SymNormLoad.Supplement
