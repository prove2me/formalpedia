-- Prove2me | Theorems.Thm_RandOrderCSP_lemma_5_6
-- name    : RandOrderCSP.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:10:35.770825+00:00
-- url     : https://prove2.me/theorems/3a7c2109-e1ec-4031-a971-7eec0dca3ce4
-- title:
--   Lemma 5.6 — boundedness implies uniformity
-- statement:
--   Fix $q,k\ge2$ and a $k$-uniform $\Delta_1(\mathbb Z_q^k)$-colored hypergraph $\Phi_*=(G_*,\mathcal Y_*)$. There is $\alpha_0>0$ such that for every $\varepsilon\in(0,1/2)$ and $\zeta\ge1$ there is $\tau>0$ with the following property. Let $n,s\ge1$ satisfy $2\log_q(2/\varepsilon)\le s\le\tau n$, let $\alpha\in(0,\alpha_0]$, and let $D$ be a $(\zeta,s)$-bounded distribution on $\mathbb Z_q^{\mathcal V_{G_*^n}}$. If $\Phi=(H,\mathcal Y)\sim\mathrm{Poi}(\Phi_*^n,\alpha n^{-(k-1)})$, then
--
--   $$\mathbb P_\Phi\big[\mathrm{Acy}(H)\text{ and }\|\mu_{(T_\Phi)_*D}-1\|_\infty>\varepsilon\big]\le\varepsilon.$$
--
--   While the posterior stays bounded, the next player's input is therefore nearly uniform.
--
--   Differences from the source:
--   - encoding: ‖μ − 1‖_∞ > ε → some label matrix Z has |μ(Z) − 1| > ε; reason: maximum over a finite set
--   - encoding: (ζ, s)-bounded, with the envelope defined assuming s ≤ (e²q⁴/ζ²)N → that inequality is a conjunct of the predicate; reason: the source defines the notion only under that inequality
-- source:
--   Singer, Tulsiani, Velusamy, A dichotomy theorem for approximating CSPs in random-order streams, STOC 2027 submission (manuscript sha256 3aca9d2f…), Lemma 5.6, p.24

import Mathlib
import Definitions.Def_RandOrderCSP_IsOneWiseUniform
import Definitions.Def_RandOrderCSP_compPartition
import Definitions.Def_RandOrderCSP_blowup
import Definitions.Def_RandOrderCSP_poiLaw
import Definitions.Def_RandOrderCSP_obsKernel
import Definitions.Def_RandOrderCSP_envelope

namespace RandOrderCSP

/-- **Lemma 5.6 (boundedness implies uniformity).** Singer, Tulsiani, Velusamy, *A dichotomy theorem for
approximating CSPs in random-order streams*, STOC 2027 submission (manuscript sha256 3aca9d2f…),
Lemma 5.6, p.24.

**Formalization Note.** `‖μ_{(T_Φ)_*D} − 1‖_∞ > ε` is the existence of a label matrix `Z` with
`|μ(Z) − 1| > ε`, over the finite set of matrices. `log_q` is `Real.logb q` with argument `2/ε > 0`. -/
theorem lemma_5_6 {k q : ℕ} [NeZero q] (hk : 2 ≤ k) (hq : 2 ≤ q) {V E : Type} [Fintype V]
    [DecidableEq V] [Nonempty V] [Fintype E] [DecidableEq E] (G : Hypergraph k V E)
    (Y : E → (Fin k → ZMod q) → ℝ) (hY : ∀ j, IsOneWiseUniform (Y j)) :
    ∃ α₀ : ℝ, 0 < α₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ ζ : ℝ, 1 ≤ ζ → ∃ τ : ℝ, 0 < τ ∧
        ∀ n s : ℕ, 1 ≤ n → 1 ≤ s →
          2 * Real.logb q (2 / ε) ≤ s → (s : ℝ) ≤ τ * n →
          ∀ α : ℝ, 0 < α → α ≤ α₀ →
          ∀ D : (V × Fin n → ZMod q) → ℝ, IsDistr D → IsEnvBounded ζ s D →
            poiLaw (E × (Fin k → Fin n)) (poiRate α n k)
              {c | (sparsify (blowup G n) c).Acy ∧
                ∃ Z, ε < |density (pushObs (sparsify (blowup G n) c)
                  (sparsifyColor (blowupColor Y n) c) D) Z - 1|} ≤ ENNReal.ofReal ε := by sorry

end RandOrderCSP
