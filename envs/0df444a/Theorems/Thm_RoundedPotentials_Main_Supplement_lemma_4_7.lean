-- Prove2me | Theorems.Thm_RoundedPotentials_Main_Supplement_lemma_4_7
-- name    : RoundedPotentials.Main.Supplement.lemma_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:05:37.43216+00:00
-- url     : https://prove2.me/theorems/17b1b479-7c62-4ddf-b343-26e87f26594e
-- title:
--   Lemma 4.7 — Sorted clipped-sum evaluation
-- statement:
--   Let $F$ be a commutative ring; in the paper $F=\mathbb F_P$. Take $n\ge1$, an integer $Q_0>0$, integers $i_1,\dots,i_n$, and $\lambda_u,\alpha_j,\beta_j\in F$. Define the clipped kernels and the true value
--   $$K^+_j=\sum_u\lambda_u\,\mathrm{clip}(i_u-i_j,0,Q_0),\qquad K^-_j=\sum_u\lambda_u\,\mathrm{clip}(i_j-i_u,0,Q_0),\qquad E(\zeta)=\sum_{j=1}^n\bigl(\alpha_jK^+_j-\beta_jK^-_j\bigr).$$
--   With $\lambda_u=\vartheta_u(\zeta)$, $\alpha_j=A^+_j(\zeta)$ and $\beta_j=A^-_j(\zeta)$, this is the value of the verification polynomial (15) at the private point.
--
--   There are a single program of the two-sorted machine and constants $C,K$, independent of $F$ and of the input, with the following property. On every such input, with integer words bounded by $M^K$, the program halts with output $E(\zeta)$, and
--
--   1. it uses at most $Cn(\lfloor\log_2 n\rfloor+1)$ integer comparisons;
--   2. it uses at most $Cn$ field operations;
--   3. it writes at most $Cn$ distinct cells (additional words);
--   4. it executes at most $Cn(\lfloor\log_2 n\rfloor+1)$ other integer instructions.
--
--   This lemma lets the Merlin–Arthur verifier of Theorem 4.6 evaluate each query's polynomial check in $\widetilde O(n)$ time, instead of the $O(n^2)$ field operations of direct evaluation.
--
--   **Formalization Note** The machine is `FieldMachine`. Field values cannot be compared or converted to integers, and integer arithmetic has no division, so comparisons and field operations can only be spent through the counted instructions.
--
--   Differences from the source:
--   - generalization: λ_u = ϑ_u(ζ), α_j = A⁺_j(ζ), β_j = A⁻_j(ζ) in 𝔽_P; indices from a certificate; Q₀ = 32n²W → arbitrary λ, α, β in any commutative ring F, arbitrary integers i_u, any integer Q₀ > 0; reason: E(ζ) is the same expression; taking F = 𝔽_P and the paper's values gives the source's claim
--   - generalization: O(n log n) comparisons, O(n) field operations, O(n) additional words → the same three bounds plus a bound C·n(⌊log₂ n⌋+1) on all other integer instructions; reason: an extra conclusion, met by the sorted-prefix algorithm of the proof; dropping it gives the source's claim
--   - encoding: "can be computed using" the three resources → one uniform program of the two-sorted machine FieldMachine with three counters and the set of written cells; integer words bounded by (n + |Q₀| + max|i_u| + 2)^K; reason: makes each resource a counter and words O(log) bits
--   - encoding: O(n log n), O(n) → C·n·(⌊log₂ n⌋+1) and C·n with one constant C for all inputs; reason: explicit form of the O-bounds; n ≥ 1
-- source:
--   Ohad Trabelsi, STOC 2027 submission #1650 (October 2026), p. 22, Lemma 4.7

import Mathlib
import Definitions.Def_RoundedPotentials_Main_Supplement_FieldMachine

namespace RoundedPotentials.Main.Supplement

theorem lemma_4_7 : ∃ (P : List FInstr) (C K : ℕ),
    ∀ (F : Type) [CommRing F] (n : ℕ) (Q0 : ℤ) (i : Fin n → ℤ) (lam α β : Fin n → F),
      1 ≤ n → 0 < Q0 →
      ∃ k : ℕ,
        (frun P (wordBound K Q0 i) (finit n Q0 i lam α β) k).outcome =
            some (some (evalE Q0 i lam α β)) ∧
          (frun P (wordBound K Q0 i) (finit n Q0 i lam α β) k).cmps ≤
            C * n * (Nat.log 2 n + 1) ∧
          (frun P (wordBound K Q0 i) (finit n Q0 i lam α β) k).fops ≤ C * n ∧
          (frun P (wordBound K Q0 i) (finit n Q0 i lam α β) k).iops ≤
            C * n * (Nat.log 2 n + 1) ∧
          (frun P (wordBound K Q0 i) (finit n Q0 i lam α β) k).written.card ≤ C * n := by sorry

end RoundedPotentials.Main.Supplement
