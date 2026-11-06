-- Prove2me | Theorems.Thm_PottsRapidMixing_lemma_3_8
-- name    : PottsRapidMixing.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:56:08.025265+00:00
-- url     : https://prove2.me/theorems/02f5c25f-a5e8-4245-b571-e9e51e8790f5
-- title:
--   Lemma 3.8, p.19 — $\mathrm{KL}(P\|Q)\le C_{\mathrm{obs}}I_\rho(\nu)$
-- statement:
--   Let $\Delta\ge3$, and let either (spin case) $q\ge2$ be an integer, $\rho=\mu$, or (edge case) $q\ge1$ be real, $\rho=\phi$, with $0<\beta<\beta_u(q,\mathbb T_\Delta)$. There is $c>0$, depending only on $\Delta,q,\beta$, such that for every $R\ge1$, every finite graph $G$ of maximum degree at most $\Delta$, all orderings and every law $\nu$, the law $P$ of Definition 3.6 is absolutely continuous with respect to the law $Q$ of Definition 3.7, and
--   $$\mathrm{KL}(P\|Q)\le C_{\mathrm{obs}}\,I_\rho(\nu),\qquad C_{\mathrm{obs}}=c\,b_R\,e^{c\,b_R}.\tag{3.8}$$
--
--   Replacing the unknown conditional law inside a forward region by the reference law costs only a multiple of the aggregate local entropy.
--
--   **Formalization Note** $P$ and $Q$ are laws on the complete records, and KL and absolute continuity are the published `ConvexRMDP.kl`, `ConvexRMDP.AbsCont`.
--
--   Differences from the source:
--   - encoding: M, the standing chain of §2 → M = M(r) with r of (2.1), rOf Δ q β; reason: §2, p.9 fixes these parameters
--   - generalization: G a random Δ-regular graph (standing, p.9) → every finite graph of maximum degree at most Δ and all orderings; reason: the proof uses only the degree bound, as the constants of Lemma 3.9 show; the statement specializes to the source
--   - encoding: β < β_u (or B < B_u), with β > 0 standing → 0 < β < β_u(q, T_Δ); reason: 0 < β is standing on pp.1, 9; B = e^β
--   - reading: C_obs = O(b_R)·e^{O(b_R)} → one c = c(Δ, q, β), independent of R, with C_obs = c b_R e^{c b_R} for all R ≥ 1; reason: the natural reading of O(·) with the listed dependence (paper.md R8)
--   - reading: "q ≥ 1" in the edge case → q real, q ≥ 1; reason: needed by Lemma 2.8 and Lemma 3.5 (paper.md R4)
-- source:
--   Blanca, Gheissari, Park, Zhang, Rapid mixing of Potts Glauber dynamics throughout uniqueness, arXiv:2610.42059, Lemma 3.8, (3.8), p.19

import Mathlib
import Definitions.Def_ConvexRMDP_kl
import Definitions.Def_mm_basic
import Definitions.Def_PottsRapidMixing_Threshold
import Definitions.Def_PottsRapidMixing_RecordLaws

open scoped Classical
open Filter Topology

namespace PottsRapidMixing

/-- **Lemma 3.8** (Blanca, Gheissari, Park, Zhang, arXiv:2610.42059, p.19). The distribution `P` is absolutely
continuous with respect to `Q`. Moreover, for every `R ≥ 1` there is a constant `C_obs = O(b_R) e^{O(b_R)}`,
depending only on `Δ`, `q`, `β` and `R`, such that `KL(P‖Q) ≤ C_obs I_ρ(ν)`, (3.8).

**Formalization Note.** Both cases of Definition 3.6 are in this one statement: the spin case with `q ≥ 2`
an integer, `ρ = µ`, and the edge case with `q ≥ 1` real, `ρ = ϕ`. `O(b_R) e^{O(b_R)}` is read as: one
`c = c(Δ, q, β)`, independent of `R`, with `C_obs ≤ c b_R e^{c b_R}` for all `R ≥ 1`. `P` and `Q` are laws
on the complete records, for any graph of maximum degree at most `Δ` and any orderings. -/
theorem lemma_3_8 (Δ : ℕ) (hΔ : 3 ≤ Δ) :
    (∀ (q : ℕ) (β : ℝ), 2 ≤ q → 0 < β → β < betaU (q : ℝ) Δ →
      ∃ c : ℝ, 0 < c ∧ ∀ R : ℕ, 1 ≤ R →
        ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V), (∀ v, G.degree v ≤ Δ) →
        ∀ (ord : ExplOrder G) (ν : (V → Fin q) → ℝ), MarkovMixing.IsDist ν →
          ConvexRMDP.AbsCont
            (fun ρ : {ρ // ρ ∈ completeRecords ord} =>
              histProb ν (spinLik β (rOf Δ (q : ℝ) β)) ρ.1)
            (fun ρ : {ρ // ρ ∈ completeRecords ord} =>
              qRecord ord R ν (spinLik β (rOf Δ (q : ℝ) β))
                (spinInner R β (rOf Δ (q : ℝ) β)) ρ.1) ∧
          ConvexRMDP.kl
            (fun ρ : {ρ // ρ ∈ completeRecords ord} =>
              histProb ν (spinLik β (rOf Δ (q : ℝ) β)) ρ.1)
            (fun ρ : {ρ // ρ ∈ completeRecords ord} =>
              qRecord ord R ν (spinLik β (rOf Δ (q : ℝ) β))
                (spinInner R β (rOf Δ (q : ℝ) β)) ρ.1)
            ≤ c * bR Δ R * Real.exp (c * bR Δ R) * localEntropy (pottsLaw G β q) ν) ∧
    (∀ (q β : ℝ), 1 ≤ q → 0 < β → β < betaU q Δ →
      ∃ c : ℝ, 0 < c ∧ ∀ R : ℕ, 1 ≤ R →
        ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V), (∀ v, G.degree v ≤ Δ) →
        ∀ (ord : ExplOrder G) (ν : (G.edgeSet → Bool) → ℝ), MarkovMixing.IsDist ν →
          ConvexRMDP.AbsCont
            (fun ρ : {ρ // ρ ∈ completeRecords ord} => histProb ν edgeLik ρ.1)
            (fun ρ : {ρ // ρ ∈ completeRecords ord} =>
              qRecord ord R ν edgeLik (edgeInner R (pOf β) q) ρ.1) ∧
          ConvexRMDP.kl
            (fun ρ : {ρ // ρ ∈ completeRecords ord} => histProb ν edgeLik ρ.1)
            (fun ρ : {ρ // ρ ∈ completeRecords ord} =>
              qRecord ord R ν edgeLik (edgeInner R (pOf β) q) ρ.1)
            ≤ c * bR Δ R * Real.exp (c * bR Δ R) * localEntropy (rcLaw G (pOf β) q) ν) := by sorry

end PottsRapidMixing
