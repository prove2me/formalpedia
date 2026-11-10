-- Prove2me | Theorems.Thm_SmoothedPlanted_FFK_lemma_42
-- name    : SmoothedPlanted.FFK.lemma_42
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:34:40.722657+00:00
-- url     : https://prove2.me/theorems/b5a68230-3237-4852-9254-43ed79d16d86
-- title:
--   Lemma 42 — threshold rounding recovers S up to ηk errors when Θ(H_{V\S}) ⩽ ηk/2
-- statement:
--   In the planted setting of Lemma 39, take any optimal lifted SDP solution, let $g(i)$ be its variable mass, and define $\widehat S=\{i:g(i)\ge1/2\}$. If $\eta>0$ and
--   $$\Theta(H_{V\setminus S},k,\Delta)\le\eta k/2,$$
--   then both
--   $$|\widehat S\cap S|\ge(1-\eta)k,\qquad |\widehat S|\le(1+\eta)k.$$
--   This states the threshold recovery guarantee, including ties at one half.
--
--   Differences from the source:
--   - encoding: finite variables and alphabet → variables and alphabet indexed by Fin n and Fin q; unordered pairs represented by i < j; reason: finite relabelling is bijective and counts every pair once
--   - generalization: labels y of a fixed CSP type, with symmetric relations R_y → all symmetric Boolean relations are available as labels; reason: pushforward along y ↦ R_y preserves every constraint and violation probability; each original type is a subclass
--   - encoding: unit u and vectors w in arbitrary finite dimension → positive semidefinite Gram matrix indexed by Option of the vertex type (literals in the lifted program); reason: every such vector family has this Gram matrix and each PSD matrix has a finite-dimensional realization; none is u
--   - encoding: sum over unordered edges and ordered distinct literal pairs → one half of the adjacency sum and the full ordered distinct-pair sum; reason: symmetric Gram entries count each unordered edge twice; the bounds remain Δ and k(k−1)
--   - encoding: planted setting of Lemma 39 used in Lemmas 40 and 42 → explicit S.card = k, k ≥ 1, Δ ≥ 0 and a Δ-consistent planted assignment; reason: these are the standing hypotheses of the rounding analysis, not facts assumed from a target lemma
-- source:
--   Kothari, Louis, Paul and Raghavendra, Recovering Planted Subgraphs in Smoothed Models, November 3, 2026, Lemma 42, printed p. 26 (PDF p. 28), PDF SHA256 0f9dc5d96e197a1868bf10cade60fcb647db289ebc51985e4d167c942c54f82b

import Definitions.Def_SmoothedPlanted_FFK_Rounding
import Definitions.Def_SmoothedPlanted_FFK_Incompatibility
import Definitions.Def_SmoothedPlanted_FFK_Consistent

open scoped BigOperators
open MeasureTheory ProbabilityTheory

noncomputable section

namespace SmoothedPlanted.FFK

theorem lemma_42 {n q : ℕ} (Y : CSP (Fin n) q) (S : Finset (Fin n))
    (σ : S → Fin q) (k : ℕ) (Δ η : ℝ) (hΔ : 0 ≤ Δ) (hk : 1 ≤ k)
    (hS : S.card = k) (hσ : Consistent Y S σ Δ) (hη : 0 < η)
    (M : Gram (Fin n × Fin q)) (hM : liftedOptimal (incompatibility Y) k Δ M)
    (hsmall : theta (incompatibility (restrictCSP Y Sᶜ)) k Δ ≤ η * k / 2) :
    Recovery S (roundedSet M) k η := by sorry

end SmoothedPlanted.FFK
