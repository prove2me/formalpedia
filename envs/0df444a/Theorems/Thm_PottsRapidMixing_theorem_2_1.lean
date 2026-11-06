-- Prove2me | Theorems.Thm_PottsRapidMixing_theorem_2_1
-- name    : PottsRapidMixing.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:53:44.359527+00:00
-- url     : https://prove2.me/theorems/60f4e317-77b6-49a2-9c3d-7c92dbc7e6d8
-- title:
--   Theorem 2.1, p.10 — inverse spectral gap $n\,\mathrm{polylog}(n)$
-- statement:
--   Fix integers $\Delta\ge3$, $q\ge2$ and $0<\beta<\beta_u(q,\mathbb T_\Delta)$. There are constants $\kappa,C>0$ such that with probability $1-o(1)$, a uniformly random $\Delta$-regular graph $G$ on $n$ vertices satisfies, for every $f:[q]^V\to\mathbb R$,
--   $$\mathrm{Var}_\mu(f)\le C\,n(\log n)^\kappa\,\mathcal E_{\mathrm{Gl}}(f).$$
--   That is, the inverse spectral gap of Potts Glauber dynamics is at most $n\,\mathrm{polylog}(n)$.
--
--   The variance estimate carries out the argument in its simplest setting and supplies an ingredient of the entropy proof.
--
--   Differences from the source:
--   - encoding: with probability 1 − o(1) over a uniformly random Δ-regular graph on n vertices → the fraction of Δ-regular graphs on Fin n with the property tends to 1 along n with nΔ even; reason: the uniform law exists exactly for nΔ even and n > Δ; same statement
--   - reading: constants named in a "with probability 1 − o(1)" statement → the constants are quantified before n and the graph event; reason: the stronger reading, and what the proof gives: every constant is fixed first, then G is taken in the event
--   - encoding: inverse spectral gap at most n polylog(n) → the Poincaré inequality (2.12) for all f; reason: by the variational form of the gap on p.10 this is the same claim, with no infimum
-- source:
--   Blanca, Gheissari, Park, Zhang, Rapid mixing of Potts Glauber dynamics throughout uniqueness, arXiv:2610.42059, Theorem 2.1, p.10; (2.12), p.12

import Mathlib
import Definitions.Def_LogSobolevMC_ChiSquare_Setting
import Definitions.Def_mm_mcmc
import Definitions.Def_PottsRapidMixing_Ensemble
import Definitions.Def_PottsRapidMixing_Threshold
import Definitions.Def_PottsRapidMixing_PottsLaw

open scoped Classical
open Filter Topology

namespace PottsRapidMixing

/-- **Theorem 2.1** (Blanca, Gheissari, Park, Zhang, arXiv:2610.42059, p.10). Fix integers `Δ ≥ 3`, `q ≥ 2`
and `0 < β < β_u(q, T_Δ)`. With probability `1 − o(1)`, a uniformly random Δ-regular graph on `n` vertices is
such that the inverse spectral gap of Potts Glauber dynamics at `q`, `β` is at most `n polylog(n)`.

**Formalization Note.** By the variational form on p.10 the bound is the Poincaré inequality (2.12) for all
`f`, stated here with `κ` and `C` fixed before `n`; no infimum appears. -/
theorem theorem_2_1 (Δ q : ℕ) (hΔ : 3 ≤ Δ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (hβu : β < betaU (q : ℝ) Δ) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧ WithHighProb Δ (fun n G =>
      ∀ f : (Fin n → Fin q) → ℝ,
        MarkovMixing.distVar (pottsLaw G β q) f
          ≤ C * (n : ℝ) * Real.log (n : ℝ) ^ κ *
            LogSobolevMC.ChiSquare.dirichlet (MarkovMixing.glauber (pottsLaw G β q))
              (pottsLaw G β q) f f) := by sorry

end PottsRapidMixing
