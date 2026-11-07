-- Prove2me | Theorems.Thm_RandOrderCSP_lemma_5_14
-- name    : RandOrderCSP.lemma_5_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:08:37.079001+00:00
-- url     : https://prove2.me/theorems/016097bb-abd7-42f2-9e99-4e753a378bb5
-- title:
--   Lemma 5.14 — component-potential estimate
-- statement:
--   For every $k\ge1$, $z\ge1$ and $k$-uniform hypergraph $G_*$ there are $0<\alpha_0\le1$ and $K<\infty$ with the following property. Let $n,\ell\ge1$ and $0<\alpha\le\alpha_0$. For every $V^-\subseteq\mathcal V_{G_*^n}$, if $H\sim\mathrm{Poi}(G_*^n\setminus V^-,\alpha n^{-(k-1)})$ then
--
--   $$\mathbb E\big[[\![\mathrm{Acy}(H)]\!]\,\Psi_\ell(\mathcal P_H;z)\big]\le\frac{K^\ell n^\ell}{\ell!}.$$
--
--   This controls exponential moments of component sizes over distinct blocks, which is the input needed in the proof of the inductive step.
--
--   Differences from the source:
--   - encoding: the expectation E[…] → a Lebesgue integral in ℝ≥0∞ over the count vector; reason: the integrand is nonnegative, so the bound also asserts finiteness
-- source:
--   Singer, Tulsiani, Velusamy, A dichotomy theorem for approximating CSPs in random-order streams, STOC 2027 submission (manuscript sha256 3aca9d2f…), Lemma 5.14, p.25

import Mathlib
import Definitions.Def_RandOrderCSP_compPartition
import Definitions.Def_RandOrderCSP_blockVol
import Definitions.Def_RandOrderCSP_blowup
import Definitions.Def_RandOrderCSP_poiLaw

open MeasureTheory

namespace RandOrderCSP

open scoped Classical in
/-- **Lemma 5.14 (component-potential estimate).** Singer, Tulsiani, Velusamy, *A dichotomy theorem for
approximating CSPs in random-order streams*, STOC 2027 submission (manuscript sha256 3aca9d2f…),
Lemma 5.14, p.25.

**Formalization Note.** `G∗^n \ V⁻` deletes the edges meeting `V⁻` and keeps every vertex (`deleteVerts`);
the Poisson counts live on its surviving edges. The expectation is a Lebesgue integral in `ℝ≥0∞`. -/
theorem lemma_5_14 {k : ℕ} (hk : 1 ≤ k) (z : ℝ) (hz : 1 ≤ z) {V E : Type} [Fintype V] [DecidableEq V]
    [Nonempty V] [Fintype E] (G : Hypergraph k V E) :
    ∃ α₀ K : ℝ, 0 < α₀ ∧ α₀ ≤ 1 ∧
      ∀ n ℓ : ℕ, 1 ≤ n → 1 ≤ ℓ → ∀ α : ℝ, 0 < α → α ≤ α₀ → ∀ Vm : Finset (V × Fin n),
        ∫⁻ c, (if (sparsify ((blowup G n).deleteVerts Vm) c).Acy
              then ENNReal.ofReal
                (blockPotential (sparsify ((blowup G n).deleteVerts Vm) c).compPartition z ℓ)
              else 0)
            ∂(poiLaw {j : E × (Fin k → Fin n) // ∀ i, (blowup G n).M j i ∉ Vm} (poiRate α n k)) ≤
          ENNReal.ofReal (K ^ ℓ * (n : ℝ) ^ ℓ / (ℓ.factorial : ℝ)) := by sorry

end RandOrderCSP
