-- Prove2me | Theorems.Thm_PottsRapidMixing_lemma_2_9
-- name    : PottsRapidMixing.lemma_2_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:54:53.12496+00:00
-- url     : https://prove2.me/theorems/bce6bae0-3dbd-424b-b017-c282cd23f893
-- title:
--   Lemma 2.9, p.13 — Glauber against $\widetilde M$ (entropy)
-- statement:
--   Fix $\Delta\ge3$, $q\ge2$, $\tilde B>1$ and $K>0$. There is $C>0$ such that with probability $1-o(1)$ the random $\Delta$-regular graph $G$ has the following property. For every $1<B<\tilde B$, with $\beta=\log B$ and $r=(B-1)/(\tilde B-1)$, every real $1\le L\le K\log n$ and every $f:[q]^V\to\mathbb R$,
--   $$\mathcal E_{\mathrm{Gl}}(f)\ge\frac1{CnL^\kappa}\,\mathcal H_{\widetilde M}(f^2),\qquad\kappa=2+2\Delta\log_2\tilde B.$$
--
--   This is the entropy counterpart of Lemma 2.4, with the explicit exponent $\kappa$.
--
--   Differences from the source:
--   - encoding: with probability 1 − o(1) over a uniformly random Δ-regular graph on n vertices → the fraction of Δ-regular graphs on Fin n with the property tends to 1 along n with nΔ even; reason: the uniform law exists exactly for nΔ even and n > Δ; same statement
--   - reading: constants named in a "with probability 1 − o(1)" statement → the constants are quantified before n and the graph event; reason: the stronger reading, and what the proof gives: every constant is fixed first, then G is taken in the event
--   - reading: the lemma fixes B̃ and leaves B implicit → C is quantified before B, and the graph event covers every 1 < B < B̃; reason: the proof uses only B̃ and a graph event; this is the stronger reading (paper.md R5)
-- source:
--   Blanca, Gheissari, Park, Zhang, Rapid mixing of Potts Glauber dynamics throughout uniqueness, arXiv:2610.42059, Lemma 2.9, p.13

import Mathlib
import Definitions.Def_LogSobolevMC_ChiSquare_Setting
import Definitions.Def_mm_mcmc
import Definitions.Def_PottsRapidMixing_Ensemble
import Definitions.Def_PottsRapidMixing_ChainM

open scoped Classical
open Filter Topology

namespace PottsRapidMixing

/-- **Lemma 2.9** (Blanca, Gheissari, Park, Zhang, arXiv:2610.42059, p.13). Fix `Δ ≥ 3`, `q ≥ 2`, `B̃ > 1` and
`K > 0`. There is `C > 0` such that with probability `1 − o(1)` the random Δ-regular graph is such that for
every `1 ≤ L ≤ K log n` and every `f`, `E_Gl(f) ≥ H_M̃(f²)/(C n L^κ)`, with `κ = 2 + 2Δ log₂ B̃`.

**Formalization Note.** As in Lemma 2.4, `C` is quantified before `B`, and the graph event covers every
`1 < B < B̃` with `r = (B − 1)/(B̃ − 1)`. `f` is real-valued, and the entropy functional is applied to `f²`. -/
theorem lemma_2_9 (Δ q : ℕ) (hΔ : 3 ≤ Δ) (hq : 2 ≤ q) (Bt : ℝ) (hBt : 1 < Bt) (K : ℝ) (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧ WithHighProb Δ (fun n G =>
      ∀ B : ℝ, 1 < B → B < Bt → ∀ L : ℝ, 1 ≤ L → L ≤ K * Real.log (n : ℝ) →
        ∀ f : (Fin n → Fin q) → ℝ,
          1 / (C * (n : ℝ) * L ^ (2 + 2 * (Δ : ℝ) * Real.logb 2 Bt)) *
              entMtilde G (Real.log B) q ((B - 1) / (Bt - 1)) L (fun σ => f σ ^ 2)
            ≤ LogSobolevMC.ChiSquare.dirichlet (MarkovMixing.glauber (pottsLaw G (Real.log B) q))
                (pottsLaw G (Real.log B) q) f f) := by sorry

end PottsRapidMixing
