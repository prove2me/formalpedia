-- Prove2me | Theorems.Thm_PandoraKnapsack_Skipping_theorem_5_1
-- name    : PandoraKnapsack.Skipping.theorem_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:25:17.699945+00:00
-- url     : https://prove2.me/theorems/7898d376-37b2-42fd-8375-13696ef594ef
-- title:
--   Theorem 5.1 — a polynomial-time skipping-adaptive policy within factor 32 of the fully-adaptive optimum
-- statement:
--   There is a single program $P$ of the costed machine (unit-cost real pointer machine with exact coefficient oracles for $v_i$, $p_i^j$, $\Pr[s_i^j\le r]$ and $E[\min\{s_i^j,r\}]$, uniform $[0,1]$ draws) and an exponent $k$ such that, for every valid MPK instance $I$ on the grid $\{0,\dots,T+1\}$ with any capacity $T\ge1$, any $n$ items and any $m$ choices, with $B=(n+m+\mathrm{bitlength}(T)+2)^k$:
--
--   1. for every sequence of $B$ uniform draws, $P$ halts within $B$ steps, including all optimization work, and its output decodes to a skipping-adaptive policy $\pi_I$ (no repeated item, thresholds in $\{0,\dots,T\}$);
--   2. the expected utility $E[\mathrm{utility}(\pi_I)]$, over the draws and the item sizes, exists (the integrand is integrable for the product uniform law); and
--   3. for every fully-adaptive policy $\pi$,
--   $$E[\mathrm{utility}(\pi)]\ \le\ 32\cdot E[\mathrm{utility}(\pi_I)],$$
--   so $\mathrm{ADAPT}(I)\le 32\,E[\mathrm{utility}(\pi_I)]$, i.e. $\mathrm{ADAPT}(I)/E[\mathrm{utility}(\pi_I)]=O(1)$.
--
--   The source states $O(1)$; its proof gives $8$ for Algorithm 1 with the time-indexed LP $\Psi(T)$, and Appendix B.1 replaces $\Psi(T)$ by the compact LP $\Psi_P(T)$ at a further factor $4$.
--
--   Differences from the source:
--   - reading: a polynomial-time algorithm for MPK (no machine model or input access specified) → one program of the unit-cost real pointer machine with exact coefficient access (v, p, CDF and truncated mean at real arguments) and uniform [0,1] draws, fixed before the instance, with all executed instructions at most (n + m + bitlength(T) + 2)^k for every draw sequence; optimization has no oracle instruction; reason: the declared exact-coefficient-access arithmetic reading keeps all size laws on the source grid; coefficient queries and draws each cost a step, and any optimization must be implemented and counted inside the program; no bit-complexity claim for arbitrary real coefficients is inferred
--   - reading: ADAPT(I)/E[utility(π_I)] = O(1) → ADAPT(I) ≤ 32 · E[utility(π_I)] with the explicit constant 32; reason: the constant the paper's own argument gives for the polynomial-time version: 8 from the proof of Theorem 5.1 times 4 from Appendix B.1; an explicit constant implies O(1)
--   - encoding: the ratio ADAPT(I)/E[utility(π_I)] and ADAPT(I) as a maximum → a product inequality against every fully-adaptive policy, with integrability of the utility asserted in the conclusion; reason: avoids division by zero and real-supremum defaults; the maximum is attained, so the forms are equivalent
--   - encoding: the algorithm's randomness (Bernoulli, categorical and uniform choices) → a deterministic program reading B independent uniform draws from [0,1]; the expectation is over the product uniform law; reason: every finite random choice of the algorithm is realized by uniform draws; the output policy is then a random skipping-adaptive policy as in the source
--   - encoding: skipping thresholds τ_{i,j} ∈ [0, 1] → thresholds in {0, …, T} in units of the grid; reason: on the grid the remaining capacity is an integer, so a real threshold acts like its ceiling; the output class is the source's
--   - encoding: a fully-adaptive policy chooses the next pair as an arbitrary function of the realized history (Definition 2.3) → a deterministic function from the list of attempted (item, choice, realized size) triples to stop or a next pair; re-choosing an attempted item stops; expected utility by the exact recursion over the size laws; reason: this is the source's class; randomized policies are mixtures of these and do not raise the maximum
--   - encoding: items [n] and choices [m] indexed from 1 → Fin n and Fin m, indexed from 0; reason: index shift; same instances
--   - reading: item-choice costs p_i^j paid up front (sign not stated) → 0 ≤ p_i^j in IsValid; reason: §2 calls p_i^j a cost incurred up front and Definition 2.1 divides by it; a negative cost would reward overflow, which the model never does
-- source:
--   Barak, Berlin, Cohen, Eden, Porat and Talgam-Cohen (2026), Pandora's Knapsack via Simple Policies, supplied PDF (STOC 2027 submission), SHA256 45e5830b173d687c08d5175988af81bf660c693ff805b1d2e7bc213140d27a2d, Theorem 5.1, printed p. 21 (PDF 23); constant 32 = 8 (proof of Theorem 5.1, printed p. 24, PDF 26) × 4 (Appendix B.1, printed pp. 39–41, PDF 41–43)

import Definitions.Def_PandoraKnapsack_Skipping_Machine

open MeasureTheory

namespace PandoraKnapsack.Skipping

/-- **Theorem 5.1** (Barak et al. 2026, *Pandora's Knapsack via Simple Policies*, supplied PDF,
SHA256 45e5830b…7a2d, printed p. 21, PDF 23). There exists a polynomial-time algorithm for MPK
that computes, for every instance `I`, a skipping-adaptive policy `π_I` such that
`ADAPT(I) / E[utility(π_I)] = O(1)`.

**Formalization Note.** The algorithm is one program `P` of the costed machine of
`Def_PandoraKnapsack_Skipping_Machine`, fixed before the instance; "polynomial time" is a
step bound `(n + m + bitlength(T) + 2)^k`, valid for every draw sequence. The only oracle
instructions access coefficients or draw uniform reals; all optimization work must be executed
by the program within this bound. The output must decode to a valid skipping-adaptive policy for every draw sequence.
The constant is explicit: `32 = 8 · 4`, the factor 8 of Algorithm 1 times the factor 4 lost by
the compact LP of Appendix B.1. `ADAPT(I) ≤ 32 · E[utility(π_I)]` is stated against every
fully-adaptive policy, and the expectation (over the algorithm's draws and the sizes) is
asserted to exist. -/
theorem theorem_5_1 :
    ∃ (P : Program) (k : ℕ), ∀ (n m T : ℕ) (I : Instance n m T), IsValid I →
        (∀ ω : Fin ((inputSize n m T + 2) ^ k) → unitInterval,
          Halted P (run I (extendDraws ω) P ((inputSize n m T + 2) ^ k)) ∧
          ∃ σ : SkipList n m,
            decodeOutput n m (run I (extendDraws ω) P ((inputSize n m T + 2) ^ k)).core.mem =
              some σ ∧ IsSkippingPolicy T σ) ∧
        Integrable (fun ω => skipValue I (outputPolicy I P ((inputSize n m T + 2) ^ k) ω))
          (drawLaw ((inputSize n m T + 2) ^ k)) ∧
        ∀ π : AdaptivePolicy n m,
          adaptValue I π ≤ 32 * ∫ ω, skipValue I (outputPolicy I P ((inputSize n m T + 2) ^ k) ω)
            ∂(drawLaw ((inputSize n m T + 2) ^ k)) := by sorry

end PandoraKnapsack.Skipping
