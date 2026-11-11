-- Prove2me | Theorems.Thm_SampQueryLB_WarmSLC_theorem_6
-- name    : SampQueryLB.WarmSLC.theorem_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:16:55.297225+00:00
-- url     : https://prove2.me/theorems/f8c1d990-bd28-4a10-9a2d-36d57c5502d5
-- title:
--   Theorem 6 — common degree profile of the output energies: $\langle\Xi_{i,p},\Phi_{i,p}(X)\rangle/(na_{i,p}^2)=p\sum_tB_tT_t^{p-1}+E_p$ with small $E_p$
-- statement:
--   Fix a level $0\le i\le h$ and consider a randomized algorithm, with seed $\omega$ in a standard Borel space independent of $\Xi\sim\mu_n$, making at most $q$ first-order queries $y_1,\dots,y_q$ to the field of level $i$ without gate, $x\mapsto\langle\Xi_i,\Phi_i(x)\rangle$, and outputting a point $X$ that is a Borel function of the seed and the replies ($\mathcal F_q$-measurable). Set $T_t=T_i(X,y_t)$ if $C_i(X)C_i(y_t)>0$ and $T_t=0$ otherwise.
--
--   **Theorem 6.** There exist $\mathcal F_q$-measurable real coefficients $B_1,\dots,B_q$ and random errors $(E_p)_{p\in\mathcal P}$ such that
--   $$\frac{\langle\Xi_{i,p},\Phi_{i,p}(X)\rangle}{na_{i,p}^2}=p\sum_{t=1}^qB_tT_t^{p-1}+E_p\quad\text{for every }p\in\mathcal P;$$
--   the coefficients are common to all degrees. Moreover, for every $0<\zeta<1/2$, with probability at least $1-\zeta$ under $\mu_n$ and the seed,
--   $$\max_{p\in\mathcal P}|E_p|\le\frac{C\big(\sqrt{h-i+1}\,q+\sqrt{\log(2P/\zeta)}\big)}{\sqrt n\,\min_pa_{i,p}}=o(\beta_i),$$
--   provided $q<Q$ and $\log(1/\zeta)=n^{o(1)}$, where $C>0$ is an absolute constant.
--
--   The Lean statement has two parts with the same absolute $C$: (a) for all sufficiently large $n$, every level, every $q\ge1$, every seed space and every algorithm, there are measurable $B_t$ (functions of seed and replies) such that, for every $\zeta\in(0,1/2)$, the probability that some $p$ violates the bound is at most $\zeta$; (b) for the chosen constants and every sequence $\zeta_n\in(0,1/2)$ with $\log(1/\zeta_n)\le n^{\varepsilon}$ eventually for every $\varepsilon>0$, the bound divided by $\beta_i$ tends to $0$ uniformly over levels $i$ and $1\le q<Q$.
--
--   **Formalization Note.** The algorithm makes exactly $q$ queries (`FieldAlg`): a run that stops earlier is padded with queries at the origin, where $C_i=0$, so the padded nodes are $T_t=0$ and add nothing to the representation (§5.4.1). $E_p$ is the residual of the identity, so the representation is the bound on it. The absolute constants $C_f, C_g, \eta_*, \lambda_*$ of the construction are quantified by `ForChosenConstants`: the statement holds for every $C_f\ge C_f^0$, then every $C_g\ge\max(1,C_g^0)$, then every $\eta_*\in(0,\min(1,\eta^0)]$, $\lambda_*\in(0,\min(1/2,\lambda^0)]$ with $\eta_*\lambda_*\le 1/4$ (the order and constraints of the proof of Proposition 4.2), and 'for all sufficiently large $n$' is $\exists n_0\,\forall n\ge n_0$.
--
--   Differences from the source:
--   - reading: the standing assumption of §4.1 that n is a sufficiently large integer → ∃ n0, ∀ n ≥ n0; reason: the construction is set up for large n only (§4.1); the statement itself has no constants C_f, C_g, η*, λ*
--   - encoding: x = (x_0, …, x_h) ∈ R^{d_n} with blocks x_j ∈ R^n; tensors in R^{n^{pS_i}} with ψ_i = u_i ⊗ u_{i+1}^{⊗K} ⊗ ⋯ → Point (dn n) with block j at coordinates finProdFinEquiv (j, a); G_n = EuclideanSpace on Σ (i,p), (Fin (p·S_i) → Fin n), slot r of ψ_i carrying block i + slotLevel K r; reason: a fixed labelling of coordinates and tensor slots; every statement is invariant under it
--   - reading: '= o(β_i), provided q < Q and log(1/ζ) = n^{o(1)}' → the probability bound for every q ≥ 1 and ζ ∈ (0, 1/2); the o(β_i) clause, under q < Q and log(1/ζ_n) = n^{o(1)}, as a separate conjunct for the constants of the construction; reason: §5.1 states the setting for every q; reading the proviso as governing only o(β_i) is the stronger of the two readings
--   - encoding: an algorithm making at most q queries, whose short runs are padded by zero batches → FieldAlg: exactly q queries, the query y_t a non-anticipating Borel map of the seed and the replies; reason: padding with queries at the origin gives replies (0, 0) and nodes T_t = 0 (C_i(0) = 0), so the at-most-q statement follows
--   - encoding: F_q-measurable B_t; 'with probability at least 1 − ζ'; o(β_i); max over p → measurable functions of (seed, replies); outer measure of the failure event ≤ ζ; ∀ ε > 0 eventually ≤ ε β_i uniformly in i and q < Q; ∀ p; reason: F_q = σ(ω, replies); an outer-measure upper bound is at least as strong; the definition of o
--   - reading: the absolute constants C_f, C_g, η*, λ* 'can be chosen' / are 'sufficiently large/small', n is 'a sufficiently large integer' (§4.1, proof of Proposition 4.2) → ForChosenConstants: the statement holds for all sufficiently extreme constants in the paper's choice order (C_f, then C_g ≥ 1, then η* ≤ 1, λ* ≤ 1/2, η*λ* ≤ 1/4), and for all n ≥ n0; reason: the paper fixes the constants once by monotone 'sufficiently' conditions; the for-all-sufficiently form implies the paper's existential choice and lets the thresholds of different results be combined
-- source:
--   Zhou, Suzuki, Towards the Query Complexity of Sampling under Strong Log-Concavity and Log-Sobolev Inequalities, arXiv:2611.05813 (held version dated November 3, 2026, sha256 966f8fc0…184c), p. 34, Theorem 6 (PDF p. 37)

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_SampQueryLB_WarmSLC_Model
import Definitions.Def_SampQueryLB_WarmSLC_HardFamily
import Definitions.Def_SampQueryLB_WarmSLC_Experiments

open MeasureTheory OAI.LogConcaveSampling ProbabilityTheory Filter
open scoped ENNReal ContDiff RealInnerProductSpace Topology

namespace SampQueryLB.WarmSLC

theorem theorem_6 :
    ∃ C : ℝ, 0 < C ∧
      (∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ (i : Lvl n) (q : ℕ), 1 ≤ q →
        ∀ (O : Type) [MeasurableSpace O] [StandardBorelSpace O] (μO : Measure O)
          [IsProbabilityMeasure μO] (A : FieldAlg n O q),
          ∃ B : Fin q → O × Replies n q → ℝ, (∀ t, Measurable (B t)) ∧
            ∀ ζ : ℝ, 0 < ζ → ζ < 1 / 2 →
              ((mu n).prod μO)
                {z | ¬ ∀ p : Deg n,
                  |energy z.1 i p (A.output (field z.1 i) z.2) -
                      (p.1 : ℝ) * ∑ t : Fin q, B t (z.2, A.replies (field z.1 i) z.2) *
                        Tnode i (A.output (field z.1 i) z.2) (A.queries (field z.1 i) z.2 t) ^
                          (p.1 - 1)| ≤
                    C * (Real.sqrt ((hh n - i + 1 : ℕ) : ℝ) * q +
                      Real.sqrt (Real.log (2 * PP n / ζ))) /
                      (Real.sqrt n * aMin n i)} ≤ ENNReal.ofReal ζ) ∧
      ForChosenConstants fun c =>
        ∀ ζ : ℕ → ℝ, (∀ n, 0 < ζ n ∧ ζ n < 1 / 2) →
          (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, Real.log (1 / ζ n) ≤ (n : ℝ) ^ ε) →
          ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ (i : Lvl n) (q : ℕ), 1 ≤ q → q < QQ n →
            C * (Real.sqrt ((hh n - i + 1 : ℕ) : ℝ) * q +
                Real.sqrt (Real.log (2 * PP n / ζ n))) / (Real.sqrt n * aMin n i) ≤
              ε * beta c n i := by sorry

end SampQueryLB.WarmSLC
