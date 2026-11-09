-- Prove2me | Theorems.Thm_SublinearChoresMMS_Disposal_lemma_3_2
-- name    : SublinearChoresMMS.Disposal.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T03:33:10.077092+00:00
-- url     : https://prove2.me/theorems/1fce8150-61f2-42bc-be2d-89bdc5393ef2
-- title:
--   Lemma 3.2 — a coordinated lottery with at most 2(k+1) mixed agents
-- statement:
--   Fix an absolute positive segment constant $B$. There are $C_2>0$ and a threshold $n_0$, depending only on $B$, with the following property. For $n\ge n_0$, take normalized positive distinct IDO costs, the section's $q$, and $m\ge q$ divisible by $q$. Reserve any $k$ agents, where $1\le k<n$, $q\ge4\log n$, and $k\ge C_2n\sqrt{\log n/q}$. For every ordinary agent take an actual feasible representative packing with at most $BL^3$ segments, and compute all completed bundles by the formulas of Section 3.1.
--
--   The full profile count is at most $n^5$. The computed initial coefficients sum to one, lie between $q/n$ and $2q/n$, give expected fraction $1/n$ per chore, and each completed bundle has cost at most one and fractions in $[0,1/q]$. There exists one finite law of coefficient vectors $\widehat\eta$ with
--
--   $$\mathbb E[\widehat\eta_{i,t}]=\eta_{i,t}.$$
--
--   Every supported vector is a nonnegative coefficient simplex, satisfies every chore-capacity bound, leaves at most $2(k+1)$ mixed ordinary agents, and satisfies every reserved-agent equation
--
--   $$\sum_{i\in N_o,t}\widehat\eta_{i,t}c_j(x_{i,t})=(n-k)\mathrm{PROP}_j\quad(j\in R).$$
--
--   These are outcome-wise guarantees for a finite exact-mean law. The full profile bound is a conclusion for these constructed bundles, never a hypothesis for an unrelated bundle family.
--
--   Differences from the source:
--   - generalization: the particular uniformly segmented packings constructed for Lemma 3.1 → any feasible packings with an absolute segment constant B, with constants chosen after B but before instance data; no exclusion-count restriction is needed in this coordination lemma; reason: the coordination argument uses the constructed bundles and their polynomial segment bound; Lemma 3.1 supplies one fixed B and the source packings
--   - encoding: the conditions above and the polynomial profile bound established in the proof → explicit affine equations, computed bundle bounds, and a concluded profile count at most n^5; reason: this expands the section context and computes the profiles of the actual prepared bundles instead of assuming a rounding certificate
--   - encoding: finite agents, chores, complete partitions and finite lotteries → agents Fin n, chores Fin m, allocation maps and normalized finite lists with real weights; reason: bijections identify the same finite instances and partitions; repeated lottery atoms may be merged and positive weights define support
--   - encoding: cost minimax share over labelled partitions → the negative of LittleCharity.MMS.mms evaluated at negative additive bundle costs; reason: negation exchanges finite maxima and minima; no goods nonnegativity predicate is imposed, and costShare_spec states the attained minimax characterization
-- source:
--   Zehan Lin, Xiaowei Wu, Shengwei Zhou, STOC 2027 submission #845 (October 2026), Lemma 3.2, §§3.1–3.2 and Appendix A.2, printed pp. 7–10, 26–27 / PDF pp. 8–11, 27–28; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/845.pdf

import Mathlib
import Definitions.Def_SublinearChoresMMS_Disposal_Prepared

noncomputable section

namespace SublinearChoresMMS.Disposal

/-- Lemma 3.2, printed p. 10 / PDF p. 11, with the conditions of §§3.1–3.2
expanded. The input is an actual segmented representative packing, not an arbitrary
bundle family with an assumed profile bound. All bundles are computed from it.
The constant B is the uniform segment constant in Lemma 3.1. -/
theorem lemma_3_2 (B : ℝ) (hB : 0 < B) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ (m : ℕ) (c : Cost n m),
        Normalized c → blockSize n ≤ m → blockSize n ∣ m →
        ∀ R : Finset (Fin n), 1 ≤ R.card → R.card < n →
          4 * Real.log n ≤ (blockSize n : ℝ) →
          C₂ * n * Real.sqrt (Real.log n / blockSize n) ≤ (R.card : ℝ) →
          ∀ p : Packings n m (blockSize n) R,
            (∀ i, ValidPacking c i.val (p i)) →
            (∀ i, (segments (p i) : ℝ) ≤ B * (n / blockSize n : ℕ) ^ 3) →
            (profiles c p ≤ n ^ 5) ∧
            ((∑ t : Fin (n / blockSize n), eta n (blockSize n) t) = 1) ∧
            (∀ t, (blockSize n : ℝ) / n ≤ eta n (blockSize n) t ∧
              eta n (blockSize n) t ≤ 2 * blockSize n / n) ∧
            (∀ i e, (∑ t, eta n (blockSize n) t * completed c p i t e) = 1 / (n : ℝ)) ∧
            (∀ i t, fractionalCost c i.val (completed c p i t) ≤ 1) ∧
            (∀ i t e, 0 ≤ completed c p i t e ∧ completed c p i t e ≤ 1 / (blockSize n : ℝ)) ∧
            ∃ P : FiniteLaw (Coefficients n (blockSize n) R),
              (∀ i t, P.mean (fun v => v i t) = eta n (blockSize n) t) ∧
              ∀ a : Fin P.size, 0 < P.weight a →
                Coordinated c p (P.atom a) ∧ mixedCount (P.atom a) ≤ 2 * (R.card + 1) := by sorry

end SublinearChoresMMS.Disposal
