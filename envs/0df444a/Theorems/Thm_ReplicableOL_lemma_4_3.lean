-- Prove2me | Theorems.Thm_ReplicableOL_lemma_4_3
-- name    : ReplicableOL.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:51:42.352096+00:00
-- url     : https://prove2.me/theorems/fc9b642c-accf-4a76-b93c-cac535f3f6ae
-- title:
--   Lemma 4.3 — hazard identity and hazard tail
-- statement:
--   At a fixed seed, with $M_j$ the indicator of agreement through epoch $j$, $h_j$ the hazard and $\Lambda_k=\sum_jM_{j-1}h_j$:
--
--   (a) $\mathbb E[M_{j-1}-M_j\mid\mathcal G_{j-1}]=M_{j-1}h_j$ for every $j$; hence
--   $$
--   \sum_{j\le k}\mathbb E[M_{j-1}h_j]=\mathbb E\Lambda_k=1-\mathbb EM_k=\rho(r).
--   $$
--   (b) $\sum_{j\le k}\mathbb E[M_{j-1}h^{23}_j]\le2\rho(r)$ and $\sum_{j\le k}\mathbb E[M_{j-1}h^{14}_j]\le2\rho(r)$.
--
--   (c) For every $x\ge0$, $\mathbb P[M_k=1,\Lambda_k\ge x]\le e^{-x}$; and $\mathbb P[\Lambda_k\ge x]\le\rho(r)/x$.
--
--   The first-disagreement hazards sum exactly to $\rho(r)$, with no union bound over epochs.
--
--   Differences from the source:
--   - encoding: $\mathbb P[\Lambda_k\ge x]\le\rho(r)/x$ for $x\ge0$ → the same bound for $x>0$; reason: at $x=0$ the page's right side is undefined, and Lean's $\rho/0=0$ would make it a false statement; for $\rho(r)>0$ the page reads it as $+\infty$, which says nothing
--   - generalization: the epoch rules of a learner satisfying (H2) at a fixed seed (Section 4 standing assumption, p.14) → an arbitrary `EpochRule k L`, which may read its whole current block; reason: p.17: "Within-epoch causality is not used: $\Phi_j(h;\cdot)$ may be any function of the block"; a learner's rule `𝓛.toEpochRule L r` is a special case
--   - generalization: Section 4 standing assumptions (p.14): $T=kL$, $\Delta\sqrt L\ge\sqrt3/8$ → no regime hypothesis and no condition on $L$; reason: the proof (pp.15–16, 35) uses neither; the statement specializes to the page under them
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Lemma 4.3, p.16

import Mathlib
import Definitions.Def_ReplicableOL_EpochRule
import Definitions.Def_ReplicableOL_hist
import Definitions.Def_ReplicableOL_E2
import Definitions.Def_ReplicableOL_M
import Definitions.Def_ReplicableOL_rhoR
import Definitions.Def_ReplicableOL_hazard
import Definitions.Def_ReplicableOL_selfHazard
import Definitions.Def_ReplicableOL_Lam
import Definitions.Def_ReplicableOL_fourRun
import Definitions.Def_ReplicableOL_pastField
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ReplicableOL

/-- **Lemma 4.3.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Lemma 4.3, p.16. All clauses.

**Formalization Note.** Expectations and probabilities are `E2`; the conditional identity of (a) is on `fourRun`. The second bound of (c) takes `x > 0`, where `ρ(r)/x` is defined. -/
theorem lemma_4_3 {k L : ℕ} {Δ : ℝ} (hΔ : 0 < Δ) (hΔ' : Δ ≤ 1 / 4) (Φ : EpochRule k L) :
    (∀ j : Fin k,
      (fourRun Δ k L)[fun ω => M Φ j.val ω.2.1 ω.2.2.1 - M Φ (j.val + 1) ω.2.1 ω.2.2.1 | pastField j.val]
        =ᵐ[fourRun Δ k L]
      fun ω => M Φ j.val ω.2.1 ω.2.2.1 * hazard Δ Φ j (hist ω.2.1 j) (hist ω.2.2.1 j)) ∧
    ∑ j : Fin k, E2 Δ (fun _ S S' => M Φ j.val S S' * hazard Δ Φ j (hist S j) (hist S' j)) =
      E2 Δ (fun _ S S' => Lam Δ Φ S S') ∧
    E2 Δ (fun _ S S' => Lam Δ Φ S S') = 1 - E2 Δ (fun _ S S' => M Φ k S S') ∧
    1 - E2 Δ (fun _ S S' => M Φ k S S') = rhoR Δ Φ ∧
    ∑ j : Fin k, E2 Δ (fun _ S S' => M Φ j.val S S' * selfHazard Δ Φ j (hist S' j)) ≤ 2 * rhoR Δ Φ ∧
    ∑ j : Fin k, E2 Δ (fun _ S S' => M Φ j.val S S' * selfHazard Δ Φ j (hist S j)) ≤ 2 * rhoR Δ Φ ∧
    (∀ x : ℝ, 0 ≤ x →
      E2 Δ (fun _ S S' => if M Φ k S S' = 1 ∧ x ≤ Lam Δ Φ S S' then 1 else 0) ≤ Real.exp (-x)) ∧
    (∀ x : ℝ, 0 < x →
      E2 Δ (fun _ S S' => if x ≤ Lam Δ Φ S S' then 1 else 0) ≤ rhoR Δ Φ / x) := by sorry

end ReplicableOL
