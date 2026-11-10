-- Prove2me | Theorems.Thm_SmoothedPlanted_FFK_lemma_52
-- name    : SmoothedPlanted.FFK.lemma_52
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:35:05.681202+00:00
-- url     : https://prove2.me/theorems/4b4eb7aa-4cfe-4b0f-ab54-df86011fbba6
-- title:
--   Lemma 52 — whp bound Θ(H_{V\S}, k, ∆) ⩽ κ + C1(q)√κ√(n/δ) + C2√(∆/δ)
-- statement:
--   There is a universal $C_2>0$, and for each $q\ge1$ there are $C_0,C_1,c>0$ and $N_0\ge2$, such that for every $n\ge N_0$, set $S$ of size $k$, real $\Delta>0$, certifiable $\Pi$ at $\delta>0$, and outside distributions dominating $\Pi$,
--   $$\Pr\{\Theta(H_{V\setminus S},k,\Delta)\le\kappa+C_1\sqrt\kappa\sqrt{n/\delta}+C_2\sqrt{\Delta/\delta}\}\ge1-n^{-c},\qquad\kappa=\|\Pi\|_{\rm op}/\delta.$$
--   The random graph is exactly the incompatibility graph on the outside sample, including same-variable edges. The bound is unaffected by any planted assignment or cut labels.
--
--   Differences from the source:
--   - encoding: finite variables and alphabet → variables and alphabet indexed by Fin n and Fin q; unordered pairs represented by i < j; reason: finite relabelling is bijective and counts every pair once
--   - generalization: labels y of a fixed CSP type, with symmetric relations R_y → all symmetric Boolean relations are available as labels; reason: pushforward along y ↦ R_y preserves every constraint and violation probability; each original type is a subclass
--   - encoding: unit u and vectors w in arbitrary finite dimension → positive semidefinite Gram matrix indexed by Option of the vertex type (literals in the lifted program); reason: every such vector family has this Gram matrix and each PSD matrix has a finite-dimensional realization; none is u
--   - encoding: sum over unordered edges and ordered distinct literal pairs → one half of the adjacency sum and the full ordered distinct-pair sum; reason: symmetric Gram entries count each unordered edge twice; the bounds remain Δ and k(k−1)
--   - encoding: independent outside labels distributed as D_ij → product measure of the finite relation-valued PMFs on unordered outside pairs; reason: the joint law has full independence, not just pairwise independence; all events and moments are measurable
--   - reading: with high probability → there exist c > 0 and N0 ≥ 2, chosen before the instance, with failure probability at most n^(−c) for all n ≥ N0; reason: pins the inverse-polynomial reading; enlarging the asymptotic threshold to 2 loses no asymptotic instances
--   - reading: constants C0(q), C1(q), C2 → C2 chosen before q and C0,C1 chosen after q but before all instance parameters; reason: makes the displayed dependence on the alphabet, and the universal numerical constant, explicit
--   - encoding: an instance and Δ-consistent planted assignment → the outside restriction alone, with |S|=k; reason: its graph and distribution ignore the planted assignment and cut labels; every outside table can be extended by unrestricted planted relations
--   - encoding: unspecified logarithm → natural logarithm in certifiability; reason: a fixed logarithm base is absorbed by C0
--   - encoding: Π ⪰ δ11ᵀ → Matrix.PosSemidef (Π − δ·J), which includes symmetry of Π; reason: ⪰ is the Loewner order on symmetric matrices (the paper writes S^n); a nonsymmetric Π read through its quadratic form can be replaced by (Π+Πᵀ)/2, which is still dominated by the symmetric ρ_ij, has no larger spectral norm (so κ does not grow), and keeps π_min up to a factor 2 absorbed by the existential C0
-- source:
--   Kothari, Louis, Paul and Raghavendra, Recovering Planted Subgraphs in Smoothed Models, November 3, 2026, Lemma 52, printed p. 34 (PDF p. 36), PDF SHA256 0f9dc5d96e197a1868bf10cade60fcb647db289ebc51985e4d167c942c54f82b

import Definitions.Def_SmoothedPlanted_FFK_Reweighted
import Definitions.Def_SmoothedPlanted_FFK_Certifiable
import Definitions.Def_SmoothedPlanted_FFK_Theta

open scoped BigOperators
open MeasureTheory ProbabilityTheory

noncomputable section

namespace SmoothedPlanted.FFK

theorem lemma_52 : ∃ C2 : ℝ, 0 < C2 ∧ ∀ q : ℕ, 1 ≤ q →
    ∃ C0 C1 c : ℝ, ∃ N0 : ℕ, 0 < C0 ∧ 0 < C1 ∧ 0 < c ∧ 2 ≤ N0 ∧
    ∀ (n k : ℕ) (S : Finset (Fin n)) (Δ δ : ℝ) (Pi : Matrix (Fin q) (Fin q) ℝ)
      (D : Pair (↑Sᶜ) → PMF (Relation q)),
      N0 ≤ n → S.card = k → 0 < Δ → Certifiable n C0 δ Pi → Dominates D Pi →
      1 - (n : ℝ) ^ (-c) ≤
        ((outsideLaw D) {Y | theta (incompatibility Y) k Δ ≤
          conditionNumber Pi δ + C1 * Real.sqrt (conditionNumber Pi δ) * Real.sqrt (n / δ) +
          C2 * Real.sqrt (Δ / δ)}).toReal := by sorry

end SmoothedPlanted.FFK
