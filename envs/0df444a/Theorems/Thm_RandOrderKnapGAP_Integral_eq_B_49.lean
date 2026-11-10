-- Prove2me | Theorems.Thm_RandOrderKnapGAP_Integral_eq_B_49
-- name    : RandOrderKnapGAP.Integral.eq_B_49
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:27:37.869847+00:00
-- url     : https://prove2.me/theorems/de7bc1e9-6c74-4460-9567-959ae7c58afc
-- title:
--   §B.9, Eq. (B.49) — a one-resource construction with $\Gamma_N(C,i)\ge\gamma^*-A/N$ for every horizon $N\ge 8$
-- statement:
--   Let $\gamma^*$ and $A$ be the rationals (B.48) and (B.54). For every horizon $N\ge2(D+2)=8$ (with $D=2$ the largest number of large items in a feasible configuration) there are a one-resource construction satisfying (B.7)–(B.11) and a comparison assignment satisfying (B.16) such that, for every feasible configuration $C$ of $N$ items with sizes in $[0,1]$ and every $i\in C$,
--   $$\Gamma_N(C,i)\ \ge\ \gamma^*-\frac AN .$$
--
--   This is the finite-input guarantee of the one-resource rule family (Lemma B.9 without its implementability clause). The paper's family and the verification of its rational table are computer-assisted (exact rational checker, github.com/Saksham810/IntegralGAP).
--
--   Differences from the source:
--   - reading: Γ_N(C, i) ≥ γ* − A/N for the rule family constructed in §B.5–§B.9 → for every N ≥ 2(D + 2) = 8 there exist a construction satisfying (B.7)–(B.11) and an assignment satisfying (B.16) with Γ_N(C, i) ≥ γ* − A/N for every feasible configuration C and every i ∈ C; reason: the explicit rule table is computer data the statement does not reproduce; the paper's family is a witness, and Theorem 1.1's proof uses only these properties
--   - encoding: rules ℓ, eligible sets L_k(i), (B.7) and (B.10) for the sizes, loads and thresholds that occur → rules are ℕ, L_k(s) a Finset; (B.7) and (B.10) for eligible ℓ, s ∈ [0, 1], z ∈ [0, 1] (thresholds in [0, 1)), z ↦ h measurable; μ_k probability measures with μ_k([0, 1]) = 1; inactive rounds a Bool flag; reason: the conditions are only used on these domains; measurability makes q and B expectations
--   - encoding: comparison rules ℓ_{k,C,S}(i) for every possible observed part S = C ∩ Q_k; Γ_N an expectation conditional on i ∈ Q_k → an assignment of (sizes, C, k, S, i), (B.16) for S = C ∩ Q with |Q| = k; the conditional expectation a count ratio over Perm (Fin N); reason: the comparison is analysis-only and may depend on the instance; uniform order as in §2
-- source:
--   Agrawal, Khan, Pareek, Improved Algorithms in the Random-Order Model: Knapsack, GAP, and Beyond, STOC 2027 submission (manuscript sha256 7825a05f…), p. 56 (PDF 58), §B.9, Eq. (B.49); collected in Lemma B.9, p. 64 (PDF 66)

import Mathlib
import Definitions.Def_RandOrderKnapGAP_Integral_Constants
import Definitions.Def_RandOrderKnapGAP_Integral_OneResource

namespace RandOrderKnapGAP.Integral

/-- **§B.9, Eq. (B.49)**, p. 56 (the finite-input statement proved in §B.9 and collected in
Lemma B.9, p. 64). For every horizon `N ≥ 2(D + 2) = 8` (`D = 2`, the largest number of large
items in a feasible configuration) there is a one-resource construction satisfying
(B.7)–(B.11) and a comparison assignment satisfying (B.16) such that, for every feasible
configuration `C` of `N` items with sizes in `[0, 1]` and every member `i ∈ C`,
`Γ_N(C, i) ≥ γ* − A/N`, with `γ*` and `A` the exact rationals (B.48), (B.54). -/
theorem eq_B_49 (N : ℕ) (hN : 2 * (2 + 2) ≤ N) :
    ∃ c : OneResourceConstruction, c.Valid N ∧
      ∃ ℓ : OneResourceConstruction.Assignment N, c.SatisfiesB16 N ℓ ∧
        ∀ (s : Fin N → ℝ) (C : Finset (Fin N)), OneResourceConstruction.IsConfiguration s C →
          ∀ i ∈ C, (gammaStar : ℝ) - (Aconst : ℝ) / (N : ℝ) ≤ c.Gamma N ℓ s C i := by sorry

end RandOrderKnapGAP.Integral
