-- Prove2me | Theorems.Thm_PottsRapidMixing_lemma_3_5
-- name    : PottsRapidMixing.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:55:46.451627+00:00
-- url     : https://prove2.me/theorems/554a7d5d-01d7-4027-9104-d6685248a309
-- title:
--   Lemma 3.5, p.18 — good tests are subcritical (edge case)
-- statement:
--   Let $\Delta\ge3$, real $q\ge1$, $0<\beta<\beta_u(q,\mathbb T_\Delta)$ and $s\in(s_\infty,1/d)$. There is $R\ge1$, depending only on $\Delta,q,\beta,s$, such that for the forward tree $F^+$ of a good test of $e=yv$ and an arbitrary boundary partition $\zeta$ of $\partial F^+$,
--   $$\phi^\zeta_{F^+}(\omega_e=1)\le s<1/d.\tag{3.6}$$
--
--   This is the random-cluster counterpart of Lemma 3.4.
--
--   **Formalization Note** $s<1/d$ is a hypothesis, so the second inequality of (3.6) is carried by it. A partition is a graph $\zeta$ whose edges join vertices off $F$.
--
--   Differences from the source:
--   - reading: "q ≥ 1" → q real, q ≥ 1; reason: the usual random-cluster range and the stronger reading; β_u is the printed formula at real q (paper.md R4)
--   - encoding: β < β_u (or B < B_u), with β > 0 standing → 0 < β < β_u(q, T_Δ); reason: 0 < β is standing on pp.1, 9; B = e^β
--   - encoding: s, fixed once on p.16 → hypotheses s_∞ < s < 1/d; reason: the standing choice of §3.2
--   - generalization: F⁺ the forward tree of a good test of a run of Algorithm 1 → every finite tree of the shape IsForwardTree; reason: every forward tree of a good test has this shape (p.16), so the statement specializes to the source (paper.md R9)
-- source:
--   Blanca, Gheissari, Park, Zhang, Rapid mixing of Potts Glauber dynamics throughout uniqueness, arXiv:2610.42059, Lemma 3.5, (3.6), p.18

import Mathlib
import Definitions.Def_PottsRapidMixing_Threshold
import Definitions.Def_PottsRapidMixing_RecordLaws

open scoped Classical
open Filter Topology

namespace PottsRapidMixing

/-- **Lemma 3.5** (Blanca, Gheissari, Park, Zhang, arXiv:2610.42059, p.18). Suppose `q ≥ 1` and
`β < β_u(q, T_Δ)`. There is `R ≥ 1`, depending only on `Δ`, `q`, `β`, `s`, such that for the forward tree `F⁺`
of a good test of `e = yv` and an arbitrary boundary partition `ζ` of `∂F⁺`, `ϕ^ζ_{F⁺}(ω_e = 1) ≤ s < 1/d`, (3.6).

**Formalization Note.** `q` is real, the random-cluster range, and `s ∈ (s_∞, 1/d)` is the number of p.16, so
`s < 1/d` is a hypothesis. The bound is stated for all trees of the shape `IsForwardTree`. -/
theorem lemma_3_5 (Δ : ℕ) (hΔ : 3 ≤ Δ) (q : ℝ) (hq : 1 ≤ q) (β : ℝ) (hβ : 0 < β)
    (hβu : β < betaU q Δ) (s : ℝ) (hs : sInfty Δ q β < s) (hs' : s < 1 / ((Δ : ℝ) - 1)) :
    ∃ R : ℕ, 1 ≤ R ∧ EdgeSubcritical Δ (pOf β) q s R := by sorry

end PottsRapidMixing
