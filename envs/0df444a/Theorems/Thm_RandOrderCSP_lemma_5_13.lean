-- Prove2me | Theorems.Thm_RandOrderCSP_lemma_5_13
-- name    : RandOrderCSP.lemma_5_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:08:42.23569+00:00
-- url     : https://prove2.me/theorems/8778512b-97e7-4c79-b085-c4032cbbf323
-- title:
--   Lemma 5.13 — marked component-count estimate
-- statement:
--   For every $k\ge2$, $z\ge1$ and $k$-uniform hypergraph $G_*$ there are $0<\alpha_0\le1$ and $K<\infty$ with the following property. Let $n\ge1$, $0<\alpha\le\alpha_0$, $A\subseteq\mathcal V_{G_*^n}$, $u=|A|$ and $N=n\,v_{G_*}$. For every integer $0\le\eta\le u$, if $H\sim\mathrm{Poi}(G_*^n,\alpha n^{-(k-1)})$ then
--
--   $$\mathbb E_H\big[[\![\mathrm{Acy}_A(H)]\!]\,[\![|\mathcal P_H(A)|=u-\eta]\!]\,z^{\mathrm{vol}(\mathcal P_H(A))}\big]\le K^u\Big(\alpha^{1/(k-1)}\frac uN\Big)^\eta.$$
--
--   It says the marked vertices rarely bunch up into few components, in a form strong enough to weigh the volume of those components.
--
--   Differences from the source:
--   - encoding: the expectation E_H[…] → a Lebesgue integral in ℝ≥0∞ over the count vector; reason: the integrand is nonnegative, so the bound also asserts finiteness
-- source:
--   Singer, Tulsiani, Velusamy, A dichotomy theorem for approximating CSPs in random-order streams, STOC 2027 submission (manuscript sha256 3aca9d2f…), Lemma 5.13, p.25

import Mathlib
import Definitions.Def_RandOrderCSP_compPartition
import Definitions.Def_RandOrderCSP_blockVol
import Definitions.Def_RandOrderCSP_blowup
import Definitions.Def_RandOrderCSP_poiLaw

open MeasureTheory

namespace RandOrderCSP

open scoped Classical in
/-- **Lemma 5.13 (marked component-count estimate).** Singer, Tulsiani, Velusamy, *A dichotomy theorem for
approximating CSPs in random-order streams*, STOC 2027 submission (manuscript sha256 3aca9d2f…),
Lemma 5.13, p.25.

**Formalization Note.** The expectation is a Lebesgue integral in `ℝ≥0∞` of a nonnegative integrand, so
it is not vacuous through non-integrability. `α^{1/(k-1)}` is a real power with `(k:ℝ) - 1 ≥ 1`. `0 ≤ η`
is automatic for `η : ℕ`, `u - η` has `η ≤ u`, and `0⁰ = 1` is the paper's convention. -/
theorem lemma_5_13 {k : ℕ} (hk : 2 ≤ k) (z : ℝ) (hz : 1 ≤ z) {V E : Type} [Fintype V] [DecidableEq V]
    [Nonempty V] [Fintype E] (G : Hypergraph k V E) :
    ∃ α₀ K : ℝ, 0 < α₀ ∧ α₀ ≤ 1 ∧
      ∀ n : ℕ, 1 ≤ n → ∀ α : ℝ, 0 < α → α ≤ α₀ → ∀ A : Finset (V × Fin n), ∀ η : ℕ, η ≤ A.card →
        ∫⁻ c, (if (sparsify (blowup G n) c).AcyOn A ∧
                (blockSupport (sparsify (blowup G n) c).compPartition A).card = A.card - η
              then ENNReal.ofReal (z ^ blockVol (sparsify (blowup G n) c).compPartition A)
              else 0) ∂(poiLaw (E × (Fin k → Fin n)) (poiRate α n k)) ≤
          ENNReal.ofReal (K ^ A.card *
            (α ^ (1 / ((k : ℝ) - 1)) * ((A.card : ℝ) / ((n : ℝ) * (Fintype.card V : ℝ)))) ^ η) := by sorry

end RandOrderCSP
