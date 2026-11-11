-- Prove2me | Theorems.Thm_SYKLearn_lemma_4_4
-- name    : SYKLearn.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:17:02.565662+00:00
-- url     : https://prove2.me/theorems/a1c53527-fa47-4c9c-873b-5b0aa1d6b615
-- title:
--   Lemma 4.4 — AvgScore estimates $\alpha$: $\mathrm{AvgScore}(\tilde\alpha)$ has the sign of $\tilde\alpha-\alpha$
-- statement:
--   Let $\tilde H$ be a Hermitian matrix, $\beta>0$, $\alpha\in\mathbb R$, and let $\nu$ be the law of the energy difference in Experiment 1 with measured Hamiltonian $\tilde H$ and input state $\rho_{\beta\alpha}(\tilde H)=e^{-\beta\alpha\tilde H}/\mathrm{tr}\,e^{-\beta\alpha\tilde H}$. Suppose $\nu((0,\infty))>0$. Then for every $\tilde\alpha$, with $s=\mathrm{AvgScore}(\tilde\alpha)$,
--
--   1. if $\tilde\alpha=\alpha$ then $s=0$;
--   2. if $\tilde\alpha>\alpha$ then $s>0$;
--   3. if $\tilde\alpha<\alpha$ then $s<0$.
--
--   So the unknown scale $\alpha$ is the unique zero of the average score, and its sign tells a binary search which way to move.
--
--   **Formalization Note** The input state is the physical Gibbs state; the law of Experiment 1 is defined from spectral projections.
--
--   Differences from the source:
--   - generalization: the candidate Hamiltonian H̃ = σ_n√m Σ d̂_I Γ_I of §4 and the SYK Majoranas → any Hermitian matrix K on ℂ^{2^{n/2}} and the Majoranas of any Model; reason: the proof uses only detailed balance of the Gibbs state of K, which holds for every Hermitian K; specializing K gives the page's statement
--   - generalization: §4's standing assumption α ∈ [3/4, 5/4] (p.34) → any real α; reason: (55) and its sign analysis hold for every real α; restricting α gives the page's statement
-- source:
--   Anshu–Arunachalam–Chen–Hwang, Efficiently Learning SYK Hamiltonians, STOC 2027 submission (held file sha256 5d7d199a…), Lemma 4.4, p.36 (with Lemma 4.1, p.35)

import Mathlib
import Definitions.Def_SYKLearn_Experiment

noncomputable section
open MeasureTheory SYKFastMix.FastMixing

namespace SYKLearn

/-- **Lemma 4.4 (AvgScore estimates α)**, p.36 (Anshu–Arunachalam–Chen–Hwang, *Efficiently Learning
SYK Hamiltonians*, STOC 2027 submission, held file sha256 5d7d199a…). Suppose `ν` assigns positive
probability to `(0, ∞)`, i.e. `ν((0, ∞)) > 0`. For any `α̃`, if `s = AvgScore(α̃)`:
`(α̃ = α) s = 0`, `(α̃ > α) s > 0`, `(α̃ < α) s < 0`.

**Formalization Note.** `ν` is the law of Experiment 1 (Lemma 4.1, p.35) with candidate
Hamiltonian `H̃ = K` (any Hermitian matrix on the `2^{N/2}`-dimensional space), the Majoranas of
the model, and input state `ρ = ρ_{βα}(H̃)`, the physical Gibbs state `gibbs K (β α)`. `α` is any
real number (the page's standing `α ∈ [3/4, 5/4]` is not used). `β > 0`. -/
theorem lemma_4_4 {N : ℕ} (Q : Model N) (K : Mat (SiteHilbert N)) (hK : K.IsHermitian)
    (β α : ℝ) (hβ : 0 < β)
    (hpos : 0 < energyLaw Q.γ K (gibbs K (β * α)) (Set.Ioi 0)) (α' : ℝ) :
    (α' = α → avgScore β α' (energyLaw Q.γ K (gibbs K (β * α))) = 0) ∧
    (α < α' → 0 < avgScore β α' (energyLaw Q.γ K (gibbs K (β * α)))) ∧
    (α' < α → avgScore β α' (energyLaw Q.γ K (gibbs K (β * α))) < 0) := by sorry

end SYKLearn
