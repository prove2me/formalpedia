-- Prove2me | Theorems.Thm_PottsRapidMixing_theorem_4_6
-- name    : PottsRapidMixing.theorem_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:54:46.929332+00:00
-- url     : https://prove2.me/theorems/4a209433-7e5a-4917-9582-3f315c496022
-- title:
--   Theorem 4.6, p.29 — from $\phi$ to $M$
-- statement:
--   Let $\Delta\ge3$, $q\ge2$, $\beta>0$ and $r\in(0,1)$. Suppose that on a $\Delta$-regular graph $G=(V,E)$, with $m=|E|$, there is a constant $C_{\mathrm{ent}}>1$ such that for every $h:\{0,1\}^E\to\mathbb R_{\ge0}$,
--   $$\mathrm{Ent}_\phi(h)\le C_{\mathrm{ent}}\sum_{e\in E}\mathbb E_\phi\bigl[\mathrm{Ent}(h\mid A_{-e})\bigr].\tag{4.1}$$
--   Then for every $f:[q]^V\to\mathbb R_{\ge0}$,
--   $$\mathbb E_{H\sim\mathbb P_{\mu,M}}\mathrm{Ent}_{\mu_H}(f)\ge\frac{rm}{(C_{\mathrm{ent}}+1)(m+1)}\,\mathrm{Ent}_\mu(f).\tag{4.2}$$
--
--   This transfers approximate tensorization from the edge model to entropy contraction for the chain $M$. Hypothesis (4.1) is the theorem's own.
--
--   Differences from the source:
--   - encoding: Δ ≥ 3, integer q ≥ 2 and β > 0 fixed for the whole paper (pp.1, 9); r ∈ (0, 1) arbitrary and M = M(r) (§4, p.26); ϕ at p = 1 − e^{−β} (p.9) → hypotheses 3 ≤ Δ, 2 ≤ q, 0 < β, 0 < r < 1; ϕ = rcLaw G (pOf β) q; reason: the standing assumptions of the paper and of §4, stated as binders; same instances
-- source:
--   Blanca, Gheissari, Park, Zhang, Rapid mixing of Potts Glauber dynamics throughout uniqueness, arXiv:2610.42059, Theorem 4.6, (4.1), (4.2), p.29

import Mathlib
import Definitions.Def_PottsRapidMixing_Threshold
import Definitions.Def_PottsRapidMixing_ChainM

open scoped Classical
open Filter Topology

namespace PottsRapidMixing

/-- **Theorem 4.6** (Blanca, Gheissari, Park, Zhang, arXiv:2610.42059, p.29). Suppose on a Δ-regular graph
`G = (V, E)` there is a constant `C_ent > 1` such that for every `h : {0, 1}^E → ℝ_{≥0}`,
`Ent_ϕ(h) ≤ C_ent ∑_e E_ϕ[Ent(h | A_{−e})]`, (4.1). Then for every `f : [q]^V → ℝ_{≥0}`,
`E_{H∼P_{µ,M}} Ent_{µ_H}(f) ≥ (r m/((C_ent + 1)(m + 1))) Ent_µ(f)`, (4.2), where `m = |E|`.

**Formalization Note.** `r ∈ (0, 1)` is arbitrary and `M = M(r)` (p.26). (4.1) is the paper's own hypothesis. -/
theorem theorem_4_6 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (Δ q : ℕ)
    (hΔ : 3 ≤ Δ) (hq : 2 ≤ q) (hG : G.IsRegularOfDegree Δ) (β : ℝ) (hβ : 0 < β)
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (Cent : ℝ) (hC : 1 < Cent)
    (h41 : ∀ h : (G.edgeSet → Bool) → ℝ, (∀ A, 0 ≤ h A) →
      GibbsCongestion.entropy (rcLaw G (pOf β) (q : ℝ)) h
        ≤ Cent * ∑ e : G.edgeSet, expCondEnt (rcLaw G (pOf β) (q : ℝ)) (Finset.univ.erase e) h)
    (f : (V → Fin q) → ℝ) (hf : ∀ σ, 0 ≤ f σ) :
    r * (Fintype.card G.edgeSet : ℝ) / ((Cent + 1) * ((Fintype.card G.edgeSet : ℝ) + 1)) *
        GibbsCongestion.entropy (pottsLaw G β q) f
      ≤ entM G β q r f := by sorry

end PottsRapidMixing
