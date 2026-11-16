-- Prove2me | Theorems.Thm_SingleSampleCombPI_XOS_Supplement_theorem_3_1
-- name    : SingleSampleCombPI.XOS.Supplement.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:41:22.468985+00:00
-- url     : https://prove2.me/theorems/6bd30e04-b1aa-4470-860e-c0278f9749f2
-- title:
--   Theorem 3.1 (corrected: supremal divisible benchmark) — multi-sample reduction
-- statement:
--   Let $k\ge1$. In either resource regime, let $C$ be a class of buyer types with valid one-sided supporting prices. Suppose a random-order free-disposal algorithm is $\alpha$-competitive on $C$, and a feasible $k$-sample single-item algorithm is $\beta$-competitive under a fixed real arrival order $\rho$. Algorithm 1, using Algorithm 2 as its provisional-allocation subroutine, always returns a feasible irrevocable allocation and satisfies
--   $$\mathbb E\Big[\sum_i r_i(x_i')\Big]\ge\frac{\alpha\beta}{2}\mathbb E[\mathrm{Opt}(r)].$$
--   Each buyer has $k+2$ adversarially fixed types uniformly assigned to one coordination sample, $k$ competition samples and one real slot. Replay uses the same shared randomness for all transformations; each item has an independent single-item seed. This is the full $(k+1)$-sample combinatorial-to-$k$-sample single-item reduction.
--
--   Differences from the source:
--   - correction: the maximum welfare over divisible feasible allocations in §2.1 → the immutable published supremal Opt benchmark; reason: with two buyers and one divisible item, v₁(0)=0 and v₁(x)=1 for x>0, v₂(x)=x are normalized monotone concave and admit one-sided supporting prices; welfare has supremum 2 but never attains 2; whenever a maximum exists the benchmarks agree
--   - generalization: the source valuation setting and real arrivals in index order → any class C of valid supporting-price buyers and any fixed real order ρ for which the primitive is β-competitive; reason: taking C to be the source class and ρ to be the identity recovers the whole theorem; subclasses include the source’s XOS and continuous applications
--   - generalization: Algorithm 1 is αβₖ/2-competitive → Algorithm 1 is always feasible as well as αβₖ/2-competitive; reason: feasibility is established immediately before Lemma 3.2 on PDF p. 15 and is included as an additional conclusion
--   - encoding: valuations and one-sided supporting-price maps on the source allocation domains → published Buyer, Regime and cube interfaces with real-valued functions evaluated only on the allocation domain; reason: the stored demand field is unused in noncomputational continuous statements; no support, continuity or concavity condition is added to the source valuation class
--   - encoding: expectations over random seeds, uniform permutations and independent GoG assignments → published nonnegative lower expectations in ENNReal with explicit finite averages and arbitrary probability spaces of internal seeds; reason: for measurable source payoffs these are the ordinary expectations; no finite-support or atomless-input restriction is introduced
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), Theorem 3.1, printed p. 11 / PDF p. 13; proof printed 11–15, 37–38 / PDF 13–17, 39–40.

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Online

open scoped ENNReal

namespace SingleSampleCombPI.XOS.Supplement

/-- Theorem 3.1, printed p. 11 / PDF p. 13. Algorithm 1 uses exactly
Algorithm 2's replay, one coordination sample and k competition samples;
all k+2 underlying values are permuted separately for every buyer. -/
theorem theorem_3_1 (A : Regime) {n m k : ℕ} (hk : 1 ≤ k)
    (C : Buyer m → Prop) (hC : ∀ b, C b → b.Valid A)
    (F : FDAlg A n m) (S : KSPI A n k) (α β : ℝ)
    (hF : F.FDCompetitive C α) (hSv : S.Valid) :
    (∀ (ω : (replay F).Ω) (ωs : Fin m → S.Ω) (ρ : Equiv.Perm (Fin n))
        (sc : Fin n → Buyer m) (s : Fin k → Fin n → Buyer m) (r : Fin n → Buyer m),
        (∀ t i, C (s t i)) → (∀ i, C (r i)) →
          Feasible A (alg1 (replay F) S ω ωs ρ sc s r)) ∧
    ∀ ρ : Equiv.Perm (Fin n), S.Competitive β ρ →
      ∀ V : Fin n → Fin (k + 2) → Buyer m, (∀ i t, C (V i t)) →
        ENNReal.ofReal (α * β / 2) * optExpK (A := A) V ≤
          alg1Exp (replay F) S ρ V := by sorry

end SingleSampleCombPI.XOS.Supplement
