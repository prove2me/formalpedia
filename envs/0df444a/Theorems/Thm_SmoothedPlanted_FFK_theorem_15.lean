-- Prove2me | Theorems.Thm_SmoothedPlanted_FFK_theorem_15
-- name    : SmoothedPlanted.FFK.theorem_15
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:35:50.400651+00:00
-- url     : https://prove2.me/theorems/28f63ec4-e5b3-463e-aeee-3a1db21943dc
-- title:
--   Theorem 15 — polynomial-time approximate recovery in the FFK-smoothed model
-- statement:
--   There exists a universal $C_2>0$. For every alphabet size $q\ge1$, there are $C_0,C_1>0$ and one deterministic polynomial-time algorithm, fixed before the instance. It receives only $n,k,\lfloor\Delta\rfloor_+$ and the pair relations, and returns an $n$-bit membership list. There are $c>0$ and $N_0\ge2$ such that for all $n\ge N_0$, $\eta>0$, $\Delta\ge0$, certifiable $\Pi$ at $\delta>0$, and $|S|=k$, if
--   $$k\ge\frac4\eta\left(\kappa+C_1\sqrt\kappa\sqrt{n/\delta}\right),\qquad\Delta\le\frac{\eta^2\delta k^2}{16C_2^2},\qquad\kappa=\frac{\|\Pi\|_{\rm op}}\delta,$$
--   then for every family of outside distributions with $\rho_{ij}[a,b]\ge\Pi[a,b]$, the probability of the following simultaneous event is at least $1-n^{-c}$: for every planted assignment and every full constraint table extending the sample with that assignment $\Delta$-consistent, the algorithm returns $\widehat S$ satisfying
--   $$|\widehat S\cap S|\ge(1-\eta)k,\qquad|\widehat S|\le(1+\eta)k.$$
--   Thus the arbitrary planted and cut labels can depend on the outside sample. Polynomial time is asserted by a Turing machine under the explicit binary-header and relation-table encoding; it is not a free runtime field.
--
--   Differences from the source:
--   - encoding: finite variables and alphabet → variables and alphabet indexed by Fin n and Fin q; unordered pairs represented by i < j; reason: finite relabelling is bijective and counts every pair once
--   - generalization: labels y of a fixed CSP type, with symmetric relations R_y → all symmetric Boolean relations are available as labels; reason: pushforward along y ↦ R_y preserves every constraint and violation probability; each original type is a subclass
--   - encoding: independent outside labels distributed as D_ij → product measure of the finite relation-valued PMFs on unordered outside pairs; reason: the joint law has full independence, not just pairwise independence; all events and moments are measurable
--   - reading: with high probability → there exist c > 0 and N0 ≥ 2, chosen before the instance, with failure probability at most n^(−c) for all n ≥ N0; reason: pins the inverse-polynomial reading; enlarging the asymptotic threshold to 2 loses no asymptotic instances
--   - reading: constants C0(q), C1(q), C2 → C2 chosen before q and C0,C1 chosen after q but before all instance parameters; reason: makes the displayed dependence on the alphabet, and the universal numerical constant, explicit
--   - reading: possibly adaptive cut labels and arbitrary planted part → all assignments and consistent full completions quantified inside one success event; reason: captures simultaneous robustness to adversaries that observe the outside sample
--   - reading: there exists a polynomial-time algorithm → one deterministic TM2 machine chosen after q and the constants, before the instance, with exactly n output bits; reason: the source algorithm is deterministic; its observable input is only the instance, k and Δ
--   - encoding: real violation budget Δ ≥ 0 → nonnegative integer floor of Δ passed to the binary input encoder; reason: violation counts are integers; using the smaller budget loses no consistent instance or displayed parameter bound
--   - encoding: implicit finite input representation → binary integer headers with delimiters plus n²q² relation bits and an n-bit output; reason: injective encoding has polynomial length in n and the bit lengths of its numerical parameters, with no nested pairing
--   - reading: Definition 11 does not exclude Δ=0, while the displayed algorithm uses Δ>0 → the goal includes every real Δ ≥ 0; reason: preserves the full model, with the zero-budget case handled without weakening the recovery claim
--   - encoding: unspecified logarithm → natural logarithm in certifiability; reason: a fixed logarithm base is absorbed by C0
--   - generalization: for η > 0, there exist C1(q), C2 > 0 (the constants may depend on η) → C2, C0, C1, the algorithm, c and N0 are all chosen before η; reason: the uniform statement implies the printed one for each η; the proof takes C1 from Lemma 51 and C2 = 2√2, neither depending on η
--   - encoding: Π ⪰ δ11ᵀ → Matrix.PosSemidef (Π − δ·J), which includes symmetry of Π; reason: ⪰ is the Loewner order on symmetric matrices (the paper writes S^n); a nonsymmetric Π read through its quadratic form can be replaced by (Π+Πᵀ)/2, which is still dominated by the symmetric ρ_ij, has no larger spectral norm (so κ does not grow), and keeps π_min up to a factor 2 absorbed by the existential C0
-- source:
--   Kothari, Louis, Paul and Raghavendra, Recovering Planted Subgraphs in Smoothed Models, November 3, 2026, Theorem 15, printed p. 17 (PDF p. 19), PDF SHA256 0f9dc5d96e197a1868bf10cade60fcb647db289ebc51985e4d167c942c54f82b

import Definitions.Def_SmoothedPlanted_FFK_SuccessEvent
import Definitions.Def_SmoothedPlanted_FFK_Certifiable

open scoped BigOperators
open MeasureTheory ProbabilityTheory

noncomputable section

namespace SmoothedPlanted.FFK

theorem theorem_15 : ∃ C2 : ℝ, 0 < C2 ∧ ∀ q : ℕ, 1 ≤ q →
    ∃ C0 C1 : ℝ, 0 < C0 ∧ 0 < C1 ∧ ∃ alg : RecoveryInput q → List Bool,
      Nonempty (Turing.TM2ComputableInPolyTime encodeInput id alg) ∧
      (∀ x, (alg x).length = x.n) ∧
      ∃ c : ℝ, ∃ N0 : ℕ, 0 < c ∧ 2 ≤ N0 ∧
      ∀ (n k : ℕ) (Δ δ η : ℝ) (Pi : Matrix (Fin q) (Fin q) ℝ)
        (S : Finset (Fin n)) (D : Pair (↑Sᶜ) → PMF (Relation q)),
        N0 ≤ n → 0 ≤ Δ → 0 < η → Certifiable n C0 δ Pi →
        (4 / η) * (conditionNumber Pi δ + C1 * Real.sqrt (conditionNumber Pi δ) *
          Real.sqrt (n / δ)) ≤ (k : ℝ) →
        Δ ≤ η ^ 2 * δ * (k : ℝ) ^ 2 / (16 * C2 ^ 2) →
        S.card = k → Dominates D Pi →
        1 - (n : ℝ) ^ (-c) ≤ ((outsideLaw D) (successEvent alg S k Δ η)).toReal := by sorry

end SmoothedPlanted.FFK
