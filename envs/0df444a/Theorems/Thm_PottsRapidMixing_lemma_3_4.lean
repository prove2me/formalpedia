-- Prove2me | Theorems.Thm_PottsRapidMixing_lemma_3_4
-- name    : PottsRapidMixing.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:55:53.808221+00:00
-- url     : https://prove2.me/theorems/e7ff21e2-8933-42e1-8cc9-eb046f65ec1b
-- title:
--   Lemma 3.4, p.17 — good tests are subcritical (spin case)
-- statement:
--   Let $\Delta\ge3$, $q\ge2$, $0<\beta<\beta_u(q,\mathbb T_\Delta)$ and $s\in(s_\infty,1/d)$. There is $R\ge1$, depending only on $\Delta,q,\beta,s$, such that the following holds. Let $F^+$ be the forward tree of a good test of $yv$ and $\tau$ an arbitrary spin assignment to $\partial F^+$. Sample the spins $\sigma$ on $F$ from $\mu^\tau_{F^+}$, and then sample $H$ through $\mathbb P_{\sigma,M}$. Then
--   $$\mathbb P_{\mu^\tau_{F^+},M}(yv\in H)\le s.\tag{3.1}$$
--
--   Since $s<1/d$, the exploration of the sprinkled edge set under the Potts law is subcritical at good tests.
--
--   **Formalization Note** `SpinSubcritical` quantifies over all finite trees of the shape `IsForwardTree`.
--
--   Differences from the source:
--   - encoding: M, the standing chain of §2 → M = M(r) with r of (2.1), rOf Δ q β; reason: §2, p.9 fixes these parameters
--   - encoding: β < β_u (or B < B_u), with β > 0 standing → 0 < β < β_u(q, T_Δ); reason: 0 < β is standing on pp.1, 9; B = e^β
--   - encoding: s, fixed once on p.16 → hypotheses s_∞ < s < 1/d; reason: the standing choice of §3.2
--   - generalization: F⁺ the forward tree of a good test of a run of Algorithm 1 → every finite tree of the shape IsForwardTree; reason: every forward tree of a good test has this shape (p.16), so the statement specializes to the source (paper.md R9)
-- source:
--   Blanca, Gheissari, Park, Zhang, Rapid mixing of Potts Glauber dynamics throughout uniqueness, arXiv:2610.42059, Lemma 3.4, (3.1), p.17

import Mathlib
import Definitions.Def_PottsRapidMixing_Threshold
import Definitions.Def_PottsRapidMixing_RecordLaws

open scoped Classical
open Filter Topology

namespace PottsRapidMixing

/-- **Lemma 3.4** (Blanca, Gheissari, Park, Zhang, arXiv:2610.42059, p.17). Suppose `β < β_u(q, T_Δ)`. There is
`R ≥ 1`, depending only on `Δ`, `q`, `β`, `s`, such that for the forward tree `F⁺` of a good test of `yv` and an
arbitrary spin assignment `τ` to `∂F⁺`, with spins on `F` from `µ^τ_{F⁺}` and `H` from `P_{σ,M}`,
`P_{µ^τ_{F⁺},M}(yv ∈ H) ≤ s`, (3.1).

**Formalization Note.** `s` is the fixed number in `(s_∞, 1/d)` of p.16, `M` the chain of (2.1). The bound
is stated for all trees of the shape `IsForwardTree`, which every forward tree of a good test has. -/
theorem lemma_3_4 (Δ q : ℕ) (hΔ : 3 ≤ Δ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (hβu : β < betaU (q : ℝ) Δ) (s : ℝ) (hs : sInfty Δ (q : ℝ) β < s)
    (hs' : s < 1 / ((Δ : ℝ) - 1)) :
    ∃ R : ℕ, 1 ≤ R ∧ SpinSubcritical Δ q β (rOf Δ (q : ℝ) β) s R := by sorry

end PottsRapidMixing
