-- Prove2me | Theorems.Thm_TwMSOCount_Main_lemma_D_2
-- name    : TwMSOCount.Main.lemma_D_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:49:21.067433+00:00
-- url     : https://prove2.me/theorems/5a2b1a4b-7f77-4ed1-b1f7-6d5748517bbf
-- title:
--   Lemma D.2 — sharper bit bound: counted graphs have treewidth $\le 2k+2$, bit lengths $O_\theta(\bar n(L+\log\bar n))$, time $f(\theta)\bar n^4(L+\log\bar n)^2$
-- statement:
--   Write $\bar n = n + 7(k+1)+1$ and $L$ for the total bit length of the weights.
--
--   **Lemma.** Every graph counted by a numerical table, and every candidate parent formed by the numerical parent recurrence, has treewidth at most $2k+2$: a collection $K$ of a valid context, and $K$ with a local edge pattern $F\subseteq\binom J2$ added, have $\mathrm{tw}\le 2k+2$. Consequently, all table values and arithmetic intermediates have $O_\theta(\bar n(L+\log\bar n))$-bit numerators and denominators: there is $g$ with
--   $$\mathrm{bits}(G_B(m,\tau)),\ \mathrm{bits}(U_\gamma(I,m,\tau))\le g(|\theta|)\,\bar n\,(L+\log_2\bar n)\qquad(m\le n),$$
--   and the counting and sampling programs can be chosen so that every stored rational has at most $f(|\theta|)\bar n(L+\log_2\bar n)$ bits. Table construction and each sample take $f(\theta)\bar n^4(L+\log\bar n)^2$ bit operations — for a sample, in expectation over the fair coins (see the finding attached to this mission):
--   $$\text{bit time of the counting run}\le f(|\theta|)\,\bar n^4(L+\log_2\bar n)^2,\qquad \mathbb E[\text{bit time of a sample}]\le f(|\theta|)\,\bar n^4(L+\log_2\bar n)^2,$$
--   where the counting program stores the completed numerical tables and outputs $Z_{k,n}(\psi)$ and the sampler has the exact law $W/Z_{k,n}(\psi)$ of Theorem 2.1.
--
--   Differences from the source:
--   - reading: each sample take f(θ) n̄⁴(L + log n̄)² bit operations → expected bit time of one sampler call ≤ f(θ) n̄⁴(L + log n̄)²; reason: obvious typo: a worst-case bound is impossible for an exact fair-bit sampler (probability 1/7 is not dyadic), and Theorem 2.1 and Appendix D.4 say 'expected'; finding I1
--   - encoding: every graph counted by a numerical table → the collections of valid contexts (graph-table graphs have treewidth ≤ k ≤ 2k + 2 by definition); reason: the graph-table case is immediate from the defining class
--   - encoding: O_θ(n̄(L + log n̄)) bits for table values → ∃ g : ℕ → ℕ with qbits(tab e) ≤ g(|θ|)·n̄·(L + log₂ n̄) for every existing entry of size ≤ n and every state map; reason: each table value is a partial sum of weights over a subclass of the same finite set of colored graphs, so the common-denominator bound is uniform over the state partition
--   - encoding: arithmetic intermediates; table construction and each sample take … bit operations → a program pair (P, Q) with a computable f: P outputs Z and stores the tables; every cell of P and Q at every step satisfies the bit bound; P's bit time and Q's expected bit time satisfy the displayed fourth-power bound; Q has the exact law; reason: the lemma bounds the algorithm of Theorem 2.1; the machine is the one of the goal
--   - encoding: expected bit time per sample (expectation over the fair bits) → Measurable (callCost Q …) ∧ ∫⁻ callCost ∂coinTape ≤ bound; reason: ∫⁻ is a lower integral; measurability (true for every program, as the cost depends on a finite prefix of coins) makes it the expectation
--   - encoding: log n̄ → Nat.log 2 n̄; reason: differs from log₂ n̄ by less than 1 and L ≥ 1, so the bounds agree up to a constant factor absorbed into f
--   - encoding: table construction and bounded arithmetic intermediates in the counting and sampling implementations → StoresTables in the final memory and the rational-cell bit bound throughout both the counting run and every sampler run; reason: the completed tables are present and the intermediate-value clause includes the sampler, even on long rejection paths
-- source:
--   Zou, Wang, Chang, Wang, Kuželka, Exact Counting and Sampling of Labeled Graphs of Bounded Treewidth with MSO Properties, STOC 2027 submission (manuscript sha256 2715a74f…775b), Lemma D.2, p. 33 (PDF 34)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_tw
import Definitions.Def_TwMSOCount_Main_MSO2
import Definitions.Def_TwMSOCount_Main_Weights
import Definitions.Def_TwMSOCount_Main_BGraph
import Definitions.Def_TwMSOCount_Main_Separator
import Definitions.Def_TwMSOCount_Main_Tables
import Definitions.Def_TwMSOCount_Main_Types
import Definitions.Def_TwMSOCount_Main_Machine

open MeasureTheory
open scoped ENNReal

namespace TwMSOCount.Main

theorem lemma_D_2 :
    (∀ (r k : ℕ) [NeZero r] (γ : Ctx r k) (I : Finset (Lab k)) (K : BGraph r k),
      γ.Valid → I ⊆ γ.B \ γ.BS → IsCollection γ I K →
      K.tw ≤ 2 * k + 2 ∧
      ∀ F ∈ (pairs γ.J).powerset, I = γ.B \ γ.BS → K.AddEdgesOK F →
        (K.addEdges F).tw ≤ 2 * k + 2) ∧
    (∃ g : ℕ → ℕ, ∀ (r k : ℕ) [NeZero r] (ψ : Formula r Empty), ψ.IsSentence →
      ∀ (w : Weights r) (SM : StateMap r k), SM.IsStateMap ψ →
      ∀ tab : Entry r k → ℚ≥0, SolvesRecurrences SM w tab →
      ∀ (n : ℕ) (e : Entry r k), e.Valid SM → e.size ≤ n →
        qbits ((tab e : ℚ≥0) : ℚ) ≤ g (thetaSize k ψ) * (n + 7 * (k + 1) + 1) *
          (weightLength w + Nat.log 2 (n + 7 * (k + 1) + 1))) ∧
    (∃ (P Q : Program) (f : ℕ → ℕ), Computable f ∧
      ∀ (n k r : ℕ) (hr : 0 < r), ∀ (ψ : Formula r Empty), ψ.IsSentence → ∀ (w : Weights r),
        letI : NeZero r := ⟨Nat.ne_of_gt hr⟩
        ∃ s : RunStats,
          runStats P zeroTape (Config.init (encodeInput n k r ψ w)) = some s ∧
          s.final.output = [((Z k n r ψ w : ℚ≥0) : ℚ)] ∧
          (∃ SM : StateMap r k, SM.IsStateMap ψ ∧ StoresTables SM w n s.final) ∧
          s.time ≤ f (thetaSize k ψ) * (n + 7 * (k + 1) + 1) ^ 4 *
            (weightLength w + Nat.log 2 (n + 7 * (k + 1) + 1)) ^ 2 ∧
          (∀ (t i : ℕ),
            qbits ((run P zeroTape (Config.init (encodeInput n k r ψ w)) t).reg i) ≤
              f (thetaSize k ψ) * (n + 7 * (k + 1) + 1) *
                (weightLength w + Nat.log 2 (n + 7 * (k + 1) + 1))) ∧
          (0 < Z k n r ψ w →
            coinTape {τ | callOutput Q s.final.restart τ = none} = 0 ∧
            Measurable (callCost Q s.final.restart) ∧
            (∀ (τ : ℕ → Bool) (t i : ℕ),
              qbits ((run Q τ s.final.restart t).reg i) ≤
                f (thetaSize k ψ) * (n + 7 * (k + 1) + 1) *
                  (weightLength w + Nat.log 2 (n + 7 * (k + 1) + 1))) ∧
            (∀ (G : SimpleGraph (Fin n)) (χ : Fin n → Fin r),
              PlantedSubgraphLD.tw G ≤ k → ModelsPsi G χ ψ →
              coinTape {τ | callOutput Q s.final.restart τ = some (codeGraph G χ)} =
                ENNReal.ofReal (((w.W G χ / Z k n r ψ w : ℚ≥0) : ℚ) : ℝ)) ∧
            ∫⁻ τ, callCost Q s.final.restart τ ∂coinTape ≤
              ((f (thetaSize k ψ) * (n + 7 * (k + 1) + 1) ^ 4 *
                (weightLength w + Nat.log 2 (n + 7 * (k + 1) + 1)) ^ 2 : ℕ) : ℝ≥0∞))) := by sorry

end TwMSOCount.Main
