-- Prove2me | Theorems.Thm_ReplicableOL_lemma_4_1
-- name    : ReplicableOL.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:51:20.510194+00:00
-- url     : https://prove2.me/theorems/8bfc8d3a-656b-43dc-9236-5050321616bd
-- title:
--   Lemma 4.1 — measurability and independence
-- statement:
--   Let $\theta,S,S',S'',S'''$ be as in Section 4.1: four data sequences conditionally i.i.d. given $\theta$, with $\mathcal G_j=\sigma(\mu_i,S_i,S'_i:i\le j)$. For every $j\le k$ and every epoch rule:
--
--   1. $\alpha_i,\alpha_i',p_i,p_i',M_i$ are $\mathcal G_i$-measurable for $i\le j$; hence $M_{j-1},\bar p_j,h_j,h^{23}_j,h^{14}_j,\mathrm{Cov}_j,\Lambda_j$ are $\mathcal G_{j-1}$-measurable.
--   2. $(\mu_j,S_j,S_j',S_j'',S_j''')$ is independent of $\mathcal G_{j-1}$. Given $\mu_j$, and also given $\mathcal G_{j-1}\vee\sigma(\mu_j)$, the four blocks are i.i.d. with law $\nu_{\mu_j}$. Moreover $\mathbb E[\mu_j\mid\mathcal G_{j-1}]=0$.
--   3. (Freezing.) If $\Psi(\omega,y)$ is bounded, jointly measurable and $\mathcal G_{j-1}\vee\sigma(\mu_j)$-measurable in $\omega$ for each $y$, then almost surely
--   $$
--   \mathbb E[\Psi(\cdot,(S_j,S_j',S_j'',S_j'''))\mid\mathcal G_{j-1}\vee\sigma(\mu_j)]=\int\Psi(\cdot,y)\,\nu_{\mu_j}^{\otimes4}(dy),
--   $$
--   and the same holds given $\mathcal G_{j-1}$ after integrating $\mu_j$ against $U[-\Delta,\Delta]$.
--   4. $\bar p_j=\int P_j(S_{<j};s)\,\bar\nu(ds)$, hence $\bar p_j=\mathbb E[p_j\mid S_{<j}]$, and $\Gamma$ is a function of $(\theta,S,r)$.
--
--   These facts identify the explicit $\bar p_j,\mathrm{Cov}_j,h_j,h^{14}_j,h^{23}_j$ of this formalization with the paper's conditional expectations.
--
--   **Formalization Note** Lean's objects `pbar`, `covJ`, `hazard` and `selfHazard` are defined by their explicit integrals; in this theorem they are shown a.s. equal to Mathlib's `condExp`. That $\Gamma$ is a function of $(\theta,S,r)$ is the type of `gain`.
--
--   Differences from the source:
--   - reading: $\bar p_j,\mathrm{Cov}_j,h_j,h^{14}_j,h^{23}_j$ are defined as conditional expectations, and (d) gives the formula for $\bar p_j$ → the objects are defined by explicit integrals, and this theorem states that each is a.s. the corresponding Mathlib `condExp`, one conjunct each; reason: the two presentations are equivalent, and the explicit form makes Theorem 2 elementary
--   - encoding: $\Psi$ is $\mathcal G_{j-1}\vee\sigma(\mu_j)$-measurable, integrating $\mu_j$ out (second form of (c)) → $\Psi(\omega,x,y)$ with $(\omega,x)\mapsto\Psi$ measurable for `pastField j` $\otimes$ Borel, integrated in $x$ against $U$; reason: a function measurable for $\mathcal G_{j-1}\vee\sigma(\mu_j)$ has this form; it is what "after integrating" means
--   - encoding: the $\sigma$-fields of the page with 1-based indices → `pastField j` is $\mathcal G_{j-1}$ of the paper's epoch $j+1$; $h^{14}_j$ is `selfHazard` at `hist S j`, $h^{23}_j$ at `hist S' j`; reason: Lean convention; same objects
--   - encoding: $L\ge1$ implicit in Construction C → `1 ≤ L`; reason: an epoch of length $0$ has no fraction $p_j$
--   - generalization: the epoch rules of a learner satisfying (H2) at a fixed seed (Section 4 standing assumption, p.14) → an arbitrary `EpochRule k L`, which may read its whole current block; reason: p.17: "Within-epoch causality is not used: $\Phi_j(h;\cdot)$ may be any function of the block"; a learner's rule `𝓛.toEpochRule L r` is a special case
--   - generalization: Section 4 standing assumptions (p.14): $T=kL$, $\Delta\sqrt L\ge\sqrt3/8$ → no regime hypothesis and no condition on $L$; reason: the proof (pp.15–16, 35) uses neither; the statement specializes to the page under them
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Lemma 4.1, p.15

import Mathlib
import Definitions.Def_ReplicableOL_uniformPrior
import Definitions.Def_ReplicableOL_Block
import Definitions.Def_ReplicableOL_blockWeight
import Definitions.Def_ReplicableOL_EpochRule
import Definitions.Def_ReplicableOL_hist
import Definitions.Def_ReplicableOL_frac
import Definitions.Def_ReplicableOL_M
import Definitions.Def_ReplicableOL_pbar
import Definitions.Def_ReplicableOL_covJ
import Definitions.Def_ReplicableOL_hazard
import Definitions.Def_ReplicableOL_selfHazard
import Definitions.Def_ReplicableOL_Omega4
import Definitions.Def_ReplicableOL_fourRun
import Definitions.Def_ReplicableOL_pastField
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ReplicableOL

/-- **Lemma 4.1.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Lemma 4.1, p.15. All clauses, on `fourRun` with `pastField`, plus the a.e. identities that tie the explicit `pbar`, `covJ`, `hazard`, `selfHazard` to Mathlib's `condExp`.

**Formalization Note.** 0-based epochs: `pastField j` is the paper's `G_{j−1}` for the paper's epoch `j + 1`, and `pastField (i + 1)` is `G_i` for epoch `i`. `Y` of the paper is the tuple of the four blocks of epoch `j`. The second form of (c) writes the dependence on `μ_j` through an explicit variable `x`, integrated against `U`. -/
theorem lemma_4_1 {k L : ℕ} {Δ : ℝ} (hΔ : 0 < Δ) (hΔ' : Δ ≤ 1 / 4) (hL : 1 ≤ L) (Φ : EpochRule k L) (j : Fin k) :
    -- (a), first sentence
    (∀ i : Fin k,
      Measurable[pastField (i.val + 1)] (fun ω : Omega4 k L => Φ i (hist ω.2.1 i) (ω.2.1 i)) ∧
      Measurable[pastField (i.val + 1)] (fun ω : Omega4 k L => Φ i (hist ω.2.2.1 i) (ω.2.2.1 i)) ∧
      Measurable[pastField (i.val + 1)] (fun ω : Omega4 k L => frac Φ i (hist ω.2.1 i) (ω.2.1 i)) ∧
      Measurable[pastField (i.val + 1)] (fun ω : Omega4 k L => frac Φ i (hist ω.2.2.1 i) (ω.2.2.1 i)) ∧
      Measurable[pastField (i.val + 1)] (fun ω : Omega4 k L => M Φ (i.val + 1) ω.2.1 ω.2.2.1)) ∧
    -- (a), second sentence
    (Measurable[pastField j.val] (fun ω : Omega4 k L => M Φ j.val ω.2.1 ω.2.2.1) ∧
      Measurable[pastField j.val] (fun ω : Omega4 k L => pbar Δ Φ j (hist ω.2.1 j)) ∧
      Measurable[pastField j.val] (fun ω : Omega4 k L => hazard Δ Φ j (hist ω.2.1 j) (hist ω.2.2.1 j)) ∧
      Measurable[pastField j.val] (fun ω : Omega4 k L => selfHazard Δ Φ j (hist ω.2.2.1 j)) ∧
      Measurable[pastField j.val] (fun ω : Omega4 k L => selfHazard Δ Φ j (hist ω.2.1 j)) ∧
      Measurable[pastField j.val] (fun ω : Omega4 k L => covJ Δ Φ j (hist ω.2.1 j)) ∧
      Measurable[pastField j.val] (fun ω : Omega4 k L =>
        ∑ i ∈ Finset.univ.filter (fun i : Fin k => i ≤ j),
          M Φ i.val ω.2.1 ω.2.2.1 * hazard Δ Φ i (hist ω.2.1 i) (hist ω.2.2.1 i))) ∧
    -- (b)
    (Indep (MeasurableSpace.comap (fun ω : Omega4 k L =>
        (ω.1 j, ω.2.1 j, ω.2.2.1 j, ω.2.2.2.1 j, ω.2.2.2.2 j)) inferInstance)
      (pastField j.val) (fourRun Δ k L)) ∧
    (∀ y : Block L × Block L × Block L × Block L,
      (fourRun Δ k L)[fun ω => if (ω.2.1 j, ω.2.2.1 j, ω.2.2.2.1 j, ω.2.2.2.2 j) = y then (1 : ℝ) else 0 |
          MeasurableSpace.comap (fun ω : Omega4 k L => ω.1 j) inferInstance] =ᵐ[fourRun Δ k L]
        fun ω => blockWeight (ω.1 j) y.1 * blockWeight (ω.1 j) y.2.1 *
          blockWeight (ω.1 j) y.2.2.1 * blockWeight (ω.1 j) y.2.2.2) ∧
    (∀ y : Block L × Block L × Block L × Block L,
      (fourRun Δ k L)[fun ω => if (ω.2.1 j, ω.2.2.1 j, ω.2.2.2.1 j, ω.2.2.2.2 j) = y then (1 : ℝ) else 0 |
          pastField j.val ⊔ MeasurableSpace.comap (fun ω : Omega4 k L => ω.1 j) inferInstance] =ᵐ[fourRun Δ k L]
        fun ω => blockWeight (ω.1 j) y.1 * blockWeight (ω.1 j) y.2.1 *
          blockWeight (ω.1 j) y.2.2.1 * blockWeight (ω.1 j) y.2.2.2) ∧
    ((fourRun Δ k L)[fun ω => ω.1 j | pastField j.val] =ᵐ[fourRun Δ k L] 0) ∧
    -- (c), given `G_{j−1} ∨ σ(μ_j)`
    (∀ Ψ : Omega4 k L → Block L × Block L × Block L × Block L → ℝ,
      (∃ C : ℝ, ∀ ω y, |Ψ ω y| ≤ C) →
      (∀ y, Measurable[pastField j.val ⊔ MeasurableSpace.comap (fun ω : Omega4 k L => ω.1 j) inferInstance]
        (fun ω => Ψ ω y)) →
      (fourRun Δ k L)[fun ω => Ψ ω (ω.2.1 j, ω.2.2.1 j, ω.2.2.2.1 j, ω.2.2.2.2 j) |
          pastField j.val ⊔ MeasurableSpace.comap (fun ω : Omega4 k L => ω.1 j) inferInstance] =ᵐ[fourRun Δ k L]
        fun ω => ∑ y, Ψ ω y * (blockWeight (ω.1 j) y.1 * blockWeight (ω.1 j) y.2.1 *
          blockWeight (ω.1 j) y.2.2.1 * blockWeight (ω.1 j) y.2.2.2)) ∧
    -- (c), given `G_{j−1}`, after integrating `μ_j`
    (∀ Ψ : Omega4 k L → ℝ → Block L × Block L × Block L × Block L → ℝ,
      (∃ C : ℝ, ∀ ω x y, |Ψ ω x y| ≤ C) →
      (∀ y, Measurable[MeasurableSpace.prod (pastField j.val) inferInstance]
        (fun q : Omega4 k L × ℝ => Ψ q.1 q.2 y)) →
      (fourRun Δ k L)[fun ω => Ψ ω (ω.1 j) (ω.2.1 j, ω.2.2.1 j, ω.2.2.2.1 j, ω.2.2.2.2 j) | pastField j.val]
          =ᵐ[fourRun Δ k L]
        fun ω => ∫ x, ∑ y, Ψ ω x y * (blockWeight x y.1 * blockWeight x y.2.1 *
          blockWeight x y.2.2.1 * blockWeight x y.2.2.2) ∂(uniformPrior Δ)) ∧
    -- (d), and the explicit versions of the conditional objects
    ((fourRun Δ k L)[fun ω => frac Φ j (hist ω.2.1 j) (ω.2.1 j) | pastField j.val] =ᵐ[fourRun Δ k L]
      fun ω => pbar Δ Φ j (hist ω.2.1 j)) ∧
    ((fourRun Δ k L)[fun ω => frac Φ j (hist ω.2.1 j) (ω.2.1 j) |
        MeasurableSpace.comap (fun ω : Omega4 k L => hist ω.2.1 j) inferInstance] =ᵐ[fourRun Δ k L]
      fun ω => pbar Δ Φ j (hist ω.2.1 j)) ∧
    ((fourRun Δ k L)[fun ω => ω.1 j * frac Φ j (hist ω.2.1 j) (ω.2.1 j) | pastField j.val] =ᵐ[fourRun Δ k L]
      fun ω => covJ Δ Φ j (hist ω.2.1 j)) ∧
    ((fourRun Δ k L)[fun ω => if Φ j (hist ω.2.1 j) (ω.2.1 j) ≠ Φ j (hist ω.2.2.1 j) (ω.2.2.1 j) then (1 : ℝ) else 0 |
        pastField j.val] =ᵐ[fourRun Δ k L]
      fun ω => hazard Δ Φ j (hist ω.2.1 j) (hist ω.2.2.1 j)) ∧
    ((fourRun Δ k L)[fun ω => if Φ j (hist ω.2.1 j) (ω.2.1 j) ≠ Φ j (hist ω.2.1 j) (ω.2.2.2.2 j) then (1 : ℝ) else 0 |
        pastField j.val] =ᵐ[fourRun Δ k L]
      fun ω => selfHazard Δ Φ j (hist ω.2.1 j)) ∧
    ((fourRun Δ k L)[fun ω => if Φ j (hist ω.2.2.1 j) (ω.2.2.1 j) ≠ Φ j (hist ω.2.2.1 j) (ω.2.2.2.1 j) then (1 : ℝ) else 0 |
        pastField j.val] =ᵐ[fourRun Δ k L]
      fun ω => selfHazard Δ Φ j (hist ω.2.2.1 j)) := by sorry

end ReplicableOL
