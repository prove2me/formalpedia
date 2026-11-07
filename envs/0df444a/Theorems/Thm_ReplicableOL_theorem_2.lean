-- Prove2me | Theorems.Thm_ReplicableOL_theorem_2
-- name    : ReplicableOL.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:50:57.189483+00:00
-- url     : https://prove2.me/theorems/3ff2f898-1dde-4e7d-851e-94b0d638c68e
-- title:
--   Theorem 2 (formal) — online replicable composition
-- statement:
--   Consider Construction C with $T=kL$ and $\Delta\sqrt L\ge\sqrt3/8$, and any learner satisfying (H2) and epoch-level causality; no replicability is assumed. Fix a seed value $r$, let runs 1 and 2 use data $S$ and $S'$ and the seed $r$, and let $\mathrm{Cov}_j:=\mathbb E[\mu_jp_j\mid\mathcal G_{j-1}]$. Then:
--
--   1. $\sum_{j\le k}\mathbb E[M_{j-1}-M_j]=\mathbb E\Lambda_k=\rho(r)$, and $\mathbb P[M_k=1,\Lambda_k\ge x]\le e^{-x}$ for $x\ge0$.
--   2. $\sum_{j\le k}\mathbb E[M_{j-1}\cdot2L|\mathrm{Cov}_j|]\le4C_B\rho(r)\Delta^2L^{3/2}$.
--   3. $\sum_{j\le k}\mathbb E[M_{j-1}(p_j-\bar p_j)^2]\le2C_B\Delta\sqrt L\rho(r)$.
--   4. For every $\delta\in(0,1)$, with $B_\delta(x):=\frac8\delta C_B\Delta^2L^{3/2}x+4L\Delta\sqrt{C_B\Delta\sqrt L\,x/\delta}$,
--   $$
--   \mathbb P[M_k=1,\Gamma>B_\delta(\rho(r))]\le\delta,\quad\text{hence}\quad\mathbb P_{\theta,S}[\Gamma>B_\delta(\rho(r))]\le\rho(r)+\delta.
--   $$
--   5. For every $\delta\in(0,1)$, $\mathbb P[M_k=1,\Gamma>(4C_B\Delta^2L^{3/2}+(4\sqrt{C_B\Delta\sqrt L}+5)L\Delta)\log\frac2\delta]\le\delta$.
--
--   This composition theorem sums the per-epoch gain-weighted coin bound against the exact hazard identity, across arbitrarily adaptive epochs.
--
--   **Formalization Note** An `EpochRule` is the learner at the fixed seed; it reads the earlier blocks and its whole current block, which is the epoch-level causality of the statement.
--
--   Differences from the source:
--   - generalization: any learner satisfying (H2) and epoch-level causality, at a fixed seed $r$, with $T=kL$ → an arbitrary `EpochRule k L`; reason: every such learner induces one (measurability is automatic on finite bits); p.17: "Within-epoch causality is not used: $\Phi_j(h;\cdot)$ may be any function of the block", so the rule may read its whole block
--   - encoding: $\mathbb E$, $\mathbb P$ over $(\theta,S,S')$ or $(\theta,S)$ → `E2`, `E1`: an integral over the prior of a finite sum over bits; reason: the explicit form of the same expectation
--   - reading: $\bar p_j$, $\mathrm{Cov}_j$ and $h_j$ as conditional expectations → their explicit versions `pbar`, `covJ`, `hazard`; reason: Lemma 4.1(c),(d) proves them a.s. equal (`lemma_4_1`)
--   - encoding: $L\ge1$ implicit in Construction C → `1 ≤ L`; reason: implied by the regime in any case
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Theorem 2 (formal), p.9

import Mathlib
import Definitions.Def_ReplicableOL_EpochRule
import Definitions.Def_ReplicableOL_hist
import Definitions.Def_ReplicableOL_frac
import Definitions.Def_ReplicableOL_E1
import Definitions.Def_ReplicableOL_E2
import Definitions.Def_ReplicableOL_M
import Definitions.Def_ReplicableOL_rhoR
import Definitions.Def_ReplicableOL_pbar
import Definitions.Def_ReplicableOL_covJ
import Definitions.Def_ReplicableOL_Lam
import Definitions.Def_ReplicableOL_gain
import Definitions.Def_ReplicableOL_CB
import Definitions.Def_ReplicableOL_Bdelta
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ReplicableOL

/-- **Theorem 2 (formal).** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Theorem 2 (formal), p.9. All clauses (i)–(iv′). No replicability and no within-epoch causality: the rule is an arbitrary `EpochRule`.

**Formalization Note.** `T = kL`, and the learner at the fixed seed `r` is the rule `Φ`. The second form of (iv) is under `E1`, over `(θ, S)` only. `Cov_j`, `p̄_j`, `h_j` are the explicit versions, tied to `condExp` by `lemma_4_1`. `Real.log` is the natural logarithm, and `2/δ > 1`. -/
theorem theorem_2 {k L : ℕ} {Δ : ℝ} (hΔ : 0 < Δ) (hΔ' : Δ ≤ 1 / 4) (hL : 1 ≤ L)
    (hreg : √3 / 8 ≤ Δ * √(L : ℝ)) (Φ : EpochRule k L) :
    -- (i)
    ∑ j : Fin k, E2 Δ (fun _ S S' => M Φ j.val S S' - M Φ (j.val + 1) S S') = E2 Δ (fun _ S S' => Lam Δ Φ S S') ∧
    E2 Δ (fun _ S S' => Lam Δ Φ S S') = rhoR Δ Φ ∧
    (∀ x : ℝ, 0 ≤ x →
      E2 Δ (fun _ S S' => if M Φ k S S' = 1 ∧ x ≤ Lam Δ Φ S S' then 1 else 0) ≤ Real.exp (-x)) ∧
    -- (ii)
    ∑ j : Fin k, E2 Δ (fun _ S S' => M Φ j.val S S' * (2 * (L : ℝ) * |covJ Δ Φ j (hist S j)|)) ≤
      4 * CB * rhoR Δ Φ * Δ ^ 2 * (L : ℝ) ^ (3 / 2 : ℝ) ∧
    -- (iii)
    ∑ j : Fin k, E2 Δ (fun _ S S' =>
        M Φ j.val S S' * (frac Φ j (hist S j) (S j) - pbar Δ Φ j (hist S j)) ^ 2) ≤
      2 * CB * Δ * √(L : ℝ) * rhoR Δ Φ ∧
    -- (iv)
    (∀ δ : ℝ, 0 < δ → δ < 1 →
      E2 Δ (fun θ S S' => if M Φ k S S' = 1 ∧ Bdelta Δ L δ (rhoR Δ Φ) < gain Δ Φ θ S then 1 else 0) ≤ δ ∧
      E1 Δ (fun θ S => if Bdelta Δ L δ (rhoR Δ Φ) < gain Δ Φ θ S then 1 else 0) ≤ rhoR Δ Φ + δ) ∧
    -- (iv′)
    (∀ δ : ℝ, 0 < δ → δ < 1 →
      E2 Δ (fun θ S S' => if M Φ k S S' = 1 ∧
          (4 * CB * Δ ^ 2 * (L : ℝ) ^ (3 / 2 : ℝ) + (4 * √(CB * Δ * √(L : ℝ)) + 5) * (L : ℝ) * Δ) * Real.log (2 / δ)
            < gain Δ Φ θ S then 1 else 0) ≤ δ) := by sorry

end ReplicableOL
