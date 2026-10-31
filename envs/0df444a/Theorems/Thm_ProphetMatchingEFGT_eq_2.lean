-- Prove2me | Theorems.Thm_ProphetMatchingEFGT_eq_2
-- name    : ProphetMatchingEFGT.eq_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:50:50.145899+00:00
-- url     : https://prove2.me/theorems/34355a01-8c14-438d-9283-c909d4f29359
-- title:
--   Eq. (2) — $\mathbb E_{w,R}[w(R_t(w_t,F))]=\mathbb E_w[w(\mathrm{OPT}(w)\cap B_t)]$
-- statement:
--   Let $E$ be a finite ground set with a downward closed feasible family $\mathcal M$, let $(B_1,\dots,B_T)$ be an ordered partition of $E$, and let $w\sim\mu$ with integrable coordinates and independent batch blocks. Let $\mathrm{OPT}$ be a deterministic maximum-weight feasible set with measurable level sets. Draw $\tilde w^{(t)}$ independently of $w$ with the same law and set $R_t(w_t,F)=B_t\cap\mathrm{OPT}(w_t,\tilde w^{(t)})$, where $(w_t,\tilde w^{(t)})$ equals $w$ on $B_t$ and $\tilde w^{(t)}$ off $B_t$. Then for every $t$,
--   $$\mathbb E_{w,R}\big[w(R_t(w_t,F))\big]=\mathbb E_w\big[w(\mathrm{OPT}(w)\cap B_t)\big].$$
--
--   This identity turns the selectability of an OCRS for $R(w,F)$ into a fraction of the prophet's expected weight in the proof of Theorem 2.3.
--
--   Differences from the source:
--   - encoding: w̃^(t) ∼ F_{−t} → a full independent copy w̃ ∼ μ of which only the coordinates off B_t are used; reason: the used part has law F_{−t}; same expectation
--   - encoding: w ∼ F = ∏_t F_t (independence across batches, dependence within) → one law μ on E → ℝ under which the batch blocks of the partition are mutually independent (iIndepFun); reason: same instances
--   - encoding: OPT a deterministic function returning a maximum-weight feasible set (p.8, footnote 5) → any opt with opt w ∈ M, maximal weight, and measurable level sets {w | opt w = S}; reason: measurability is needed for Pr[OPT(w) = S] to be defined; the theorem holds for every such OPT
--   - encoding: finite expectations, presupposed by the ratio → Integrable coordinates / weights; reason: without it the Bochner integrals are 0 (slip 8)
-- source:
--   Ezra–Feldman–Gravin–Tang, Online Stochastic Max-Weight Matching: prophet inequality for vertex and edge arrival models, arXiv:2002.09807v2, §2.3, eq. (2) (property 5), p. 8

import Mathlib
import Definitions.Def_ProphetMatchingEFGT_BatchedModel

open MeasureTheory ProbabilityTheory

namespace ProphetMatchingEFGT

/-- **Eq. (2), p. 8 (property 5 of the sampling scheme `R(w, F)`).**
Ezra–Feldman–Gravin–Tang, *Online Stochastic Max-Weight Matching: prophet inequality for vertex and
edge arrival models*, arXiv:2002.09807v2, eq. (2), p. 8: for every `t ∈ [T]`,
`E_{w,R}[w(R_t(w_t, F))] = E_w[w(OPT(w) ∩ B_t)]`, where `R_t(w_t, F) = B_t ∩ OPT(w_t, w̃^{(t)})`
and `w̃^{(t)} ∼ F_{-t}` is drawn independently of `w`.

**Formalization Note.** The resampled vector is a full independent copy `w̃ ∼ μ` of which only the
coordinates off `B_t` are used (`hybrid`), so its relevant part has law `F_{-t}`. The standing
assumptions of §2 (downward closed `M`, independence across batches) are hypotheses. -/
theorem eq_2 {E : Type*} [Fintype E] [DecidableEq E] (M : Set (Finset E))
    (hM : IsDownwardClosed M) (μ : Measure (E → ℝ)) [IsProbabilityMeasure μ]
    (hμ : ∀ e, Integrable (fun w => w e) μ) (opt : (E → ℝ) → Finset E) (hopt : IsOPT M opt)
    (Bs : List (Finset E)) (hBs : IsOrderedPartition Bs) (hind : BlocksIndep μ Bs)
    (t : Fin Bs.length) :
    ∫ p : (E → ℝ) × (E → ℝ), setWeight p.1 (Bs.get t ∩ opt (hybrid (Bs.get t) p.1 p.2)) ∂(μ.prod μ)
      = ∫ w, setWeight w (opt w ∩ Bs.get t) ∂μ := by sorry

end ProphetMatchingEFGT
