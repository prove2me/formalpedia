-- Prove2me | Theorems.Thm_PottsRapidMixing_lemma_2_7
-- name    : PottsRapidMixing.lemma_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:54:41.03842+00:00
-- url     : https://prove2.me/theorems/cecc2221-ad63-4fa6-a00b-5115e89ad3f2
-- title:
--   Lemma 2.7, p.13 — entropy factorization for $M$
-- statement:
--   Fix $q\ge2$, $\Delta\ge3$ and $0<\beta<\beta_u(q,\mathbb T_\Delta)$, with $B=e^\beta<B_u$. There is a fixed $a(q,\Delta,B)>0$ such that with probability $1-o(1)$ over $G$, for every $f:[q]^V\to\mathbb R_{\ge0}$,
--   $$a\,\mathrm{Ent}_\mu(f)\le\mathcal H_M(f).$$
--
--   This is the entropy analogue of the constant spectral gap of $M$.
--
--   Differences from the source:
--   - encoding: with probability 1 − o(1) over a uniformly random Δ-regular graph on n vertices → the fraction of Δ-regular graphs on Fin n with the property tends to 1 along n with nΔ even; reason: the uniform law exists exactly for nΔ even and n > Δ; same statement
--   - reading: constants named in a "with probability 1 − o(1)" statement → the constants are quantified before n and the graph event; reason: the stronger reading, and what the proof gives: every constant is fixed first, then G is taken in the event
--   - encoding: M, the standing chain of §2 → M = M(r) with r of (2.1), rOf Δ q β; reason: §2, p.9 fixes these parameters
--   - encoding: β < β_u (or B < B_u), with β > 0 standing → 0 < β < β_u(q, T_Δ); reason: 0 < β is standing on pp.1, 9; B = e^β
-- source:
--   Blanca, Gheissari, Park, Zhang, Rapid mixing of Potts Glauber dynamics throughout uniqueness, arXiv:2610.42059, Lemma 2.7, p.13

import Mathlib
import Definitions.Def_PottsRapidMixing_Ensemble
import Definitions.Def_PottsRapidMixing_Threshold
import Definitions.Def_PottsRapidMixing_ChainM

open scoped Classical
open Filter Topology

namespace PottsRapidMixing

/-- **Lemma 2.7** (Blanca, Gheissari, Park, Zhang, arXiv:2610.42059, p.13). Fix `q ≥ 2`, `Δ ≥ 3` and
`B < B_u`. With probability `1 − o(1)` over `G`, there is a fixed `a(q, Δ, B) > 0` such that for every
`f : [q]^V → ℝ_{≥0}`, one has `a Ent_µ(f) ≤ H_M(f)`.

**Formalization Note.** `a` is quantified before `n`. `M` is the chain of (2.1), `r = rOf Δ q β`, with
`B = e^β`, `β > 0`. -/
theorem lemma_2_7 (Δ q : ℕ) (hΔ : 3 ≤ Δ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (hβu : β < betaU (q : ℝ) Δ) :
    ∃ a : ℝ, 0 < a ∧ WithHighProb Δ (fun n G =>
      ∀ f : (Fin n → Fin q) → ℝ, (∀ σ, 0 ≤ f σ) →
        a * GibbsCongestion.entropy (pottsLaw G β q) f ≤ entM G β q (rOf Δ (q : ℝ) β) f) := by sorry

end PottsRapidMixing
