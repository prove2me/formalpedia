-- Prove2me | Theorems.Thm_PottsRapidMixing_theorem_5_1
-- name    : PottsRapidMixing.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:54:39.242202+00:00
-- url     : https://prove2.me/theorems/87e9ae97-4127-4083-adda-2fc46261642b
-- title:
--   Theorem 5.1, p.31 — approximate tensorization of entropy for $\phi$
-- statement:
--   For integers $\Delta\ge3$ and $q\ge2$, let $0<p<p_u:=1-e^{-\beta_u}$. There is a constant $C_{\mathrm{ent}}=C_{\mathrm{ent}}(\Delta,q,p)>1$ such that with probability $1-o(1)$, a random $\Delta$-regular graph $G=(V,E)$ satisfies, for every $h:\{0,1\}^E\to\mathbb R_{\ge0}$,
--   $$\mathrm{Ent}_\phi(h)\le C_{\mathrm{ent}}\sum_{e\in E}\mathbb E_\phi\bigl[\mathrm{Ent}(h\mid A_{-e})\bigr],\tag{5.1}$$
--   where $\mathrm{Ent}(h\mid A_{-e})$ is the entropy of $h$ under $\phi(\cdot\mid A_{-e})$.
--
--   This gives a modified log-Sobolev inequality for FK dynamics throughout the uniqueness regime.
--
--   Differences from the source:
--   - encoding: with probability 1 − o(1) over a uniformly random Δ-regular graph on n vertices → the fraction of Δ-regular graphs on Fin n with the property tends to 1 along n with nΔ even; reason: the uniform law exists exactly for nΔ even and n > Δ; same statement
--   - reading: constants named in a "with probability 1 − o(1)" statement → the constants are quantified before n and the graph event; reason: the stronger reading, and what the proof gives: every constant is fixed first, then G is taken in the event
--   - encoding: p < p_u → 0 < p < p_u; reason: 0 < β is standing; p = 1 − e^{−β}
-- source:
--   Blanca, Gheissari, Park, Zhang, Rapid mixing of Potts Glauber dynamics throughout uniqueness, arXiv:2610.42059, Theorem 5.1, (5.1), p.31

import Mathlib
import Definitions.Def_PottsRapidMixing_Ensemble
import Definitions.Def_PottsRapidMixing_Threshold
import Definitions.Def_PottsRapidMixing_ChainM

open scoped Classical
open Filter Topology

namespace PottsRapidMixing

/-- **Theorem 5.1** (Blanca, Gheissari, Park, Zhang, arXiv:2610.42059, p.31). For integers `Δ ≥ 3` and `q ≥ 2`,
let `p < p_u := 1 − e^{−β_u}`. There is a constant `C_ent = C_ent(Δ, q, p) > 1` such that with probability
`1 − o(1)`, a random Δ-regular graph satisfies for every `h : {0, 1}^E → ℝ_{≥0}`,
`Ent_ϕ(h) ≤ C_ent ∑_e E_ϕ[Ent(h | A_{−e})]`, (5.1), where `Ent(h | A_{−e})` is the entropy of `h` under
`ϕ(· | A_{−e})`.

**Formalization Note.** `C_ent` is fixed before `n`. `0 < p` is the paper's `0 < β`. -/
theorem theorem_5_1 (Δ q : ℕ) (hΔ : 3 ≤ Δ) (hq : 2 ≤ q) (p : ℝ) (hp0 : 0 < p)
    (hpu : p < pU (q : ℝ) Δ) :
    ∃ Cent : ℝ, 1 < Cent ∧ WithHighProb Δ (fun n G =>
      ∀ h : (G.edgeSet → Bool) → ℝ, (∀ A, 0 ≤ h A) →
        GibbsCongestion.entropy (rcLaw G p (q : ℝ)) h
          ≤ Cent * ∑ e : G.edgeSet, expCondEnt (rcLaw G p (q : ℝ)) (Finset.univ.erase e) h) := by sorry

end PottsRapidMixing
