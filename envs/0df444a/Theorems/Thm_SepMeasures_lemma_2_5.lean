-- Prove2me | Theorems.Thm_SepMeasures_lemma_2_5
-- name    : SepMeasures.lemma_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:10:40.734955+00:00
-- url     : https://prove2.me/theorems/99b45633-f265-49ca-a86a-af6b0259578e
-- title:
--   Lemma 2.5 — the probability that two hyperplanes both strictly separate $X,Y$
-- statement:
--   Let $d\ge1$, let $X\sim\mu$ and $Y\sim\nu$ be independent, and let $K,K'$ be oriented hyperplanes with $\mu(K\cup K')=\nu(K\cup K')=0$. With $p_K=\mathbb E_\mu[\sigma_K]$, $p_{K'}=\mathbb E_\mu[\sigma_{K'}]$, $q_K=\mathbb E_\nu[\sigma_K]$, $q_{K'}=\mathbb E_\nu[\sigma_{K'}]$, $p_{KK'}=\mathbb E_\mu[\sigma_K\sigma_{K'}]$ and $q_{KK'}=\mathbb E_\nu[\sigma_K\sigma_{K'}]$,
--   $$\Pr[\text{both }K\text{ and }K'\text{ strictly separate }X,Y]=\frac{1-p_Kq_K-p_{K'}q_{K'}+p_{KK'}q_{KK'}}{4}.$$
--
--   It is used for the quantities $I_i(K)$ in the proof of Theorem 3.3.
--
--   **Formalization Note** The probability is $(\mu\otimes\nu)(\mathrm{Sep}(K)\cap\mathrm{Sep}(K'))$ as a real number.
--
--   Differences from the source:
--   - encoding: independent X ∼ µ, Y ∼ ν; Pr[·]; E_µ[σ_K] → the product measure µ.prod ν and its real-valued measure (µ.prod ν).real; Bochner integrals ∫ σ_K dµ; reason: σ_K is bounded and measurable, so the integrals are the expectations; the product measure is the law of an independent pair
-- source:
--   Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, Separating Measures by Hyperplanes (manuscript, STOC 2027 submission, sha256 96a8692407ff1815980863f3baa9c5d7b90ba27e781ed19063306f67d26fa82f), Lemma 2.5, p.13

import Mathlib
import Definitions.Def_SepMeasures_Hyp

open MeasureTheory

namespace SepMeasures

/-- Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, *Separating Measures by Hyperplanes*
(manuscript, sha256 96a86924…fa82f), Lemma 2.5, p.13: let `X ∼ μ` and `Y ∼ ν` be
independent and `K, K′` hyperplanes with `μ(K ∪ K′) = ν(K ∪ K′) = 0`. With
`p_K = E_μ[σ_K]`, `p_{K′} = E_μ[σ_{K′}]`, `q_K = E_ν[σ_K]`, `q_{K′} = E_ν[σ_{K′}]`,
`p_{KK′} = E_μ[σ_K σ_{K′}]` and `q_{KK′} = E_ν[σ_K σ_{K′}]`,
`Pr[both K and K′ strictly separate X, Y] = (1 − p_K q_K − p_{K′} q_{K′} + p_{KK′} q_{KK′})/4`.

**Formalization Note.** Independence is the product measure `μ.prod ν`; the probability is
`(μ.prod ν).real (Sep K ∩ Sep K')`. -/
theorem lemma_2_5 (d : ℕ) (hd : 1 ≤ d) (μ ν : Measure (E d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (K K' : Hyp d) (hμ : μ (K.set ∪ K'.set) = 0) (hν : ν (K.set ∪ K'.set) = 0) :
    (μ.prod ν).real (Sep K ∩ Sep K') =
      (1 - (∫ x, K.sign x ∂μ) * (∫ y, K.sign y ∂ν)
          - (∫ x, K'.sign x ∂μ) * (∫ y, K'.sign y ∂ν)
          + (∫ x, K.sign x * K'.sign x ∂μ) * (∫ y, K.sign y * K'.sign y ∂ν)) / 4 := by sorry

end SepMeasures
