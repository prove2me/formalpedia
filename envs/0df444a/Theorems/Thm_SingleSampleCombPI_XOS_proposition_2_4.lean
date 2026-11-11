-- Prove2me | Theorems.Thm_SingleSampleCombPI_XOS_proposition_2_4
-- name    : SingleSampleCombPI.XOS.proposition_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T09:08:36.976531+00:00
-- url     : https://prove2.me/theorems/88f5e237-9378-40bc-bd0c-66b89d863eaf
-- title:
--   Proposition 2.4 — layer-cake representation of the free-disposal value
-- statement:
--   For buyer types with supporting-price maps $q_1,\dots,q_n$ (in either regime) and provisional allocations $x_1,\dots,x_n\in A^m$,
--   $$\mathrm{FD}(x_1,\dots,x_n)=\sum_{j=1}^m\int_0^\infty\min\Big\{1,\ \sum_{i=1}^nx_{i,j}\,\mathbf 1[q_{i,j}(x_i)\ge w]\Big\}\,dw.$$
--
--   This is the form of the free-disposal value used in the replay comparisons of Lemmas 3.3 and 3.5.
--
--   Differences from the source:
--   - encoding: a valuation v with its supporting-price map q_v (and, for computation, oracle access) → a record Buyer m with fields v, q (supporting-price oracle) and d (demand oracle) on vectors in ℝ^m, bundles as indicator vectors; reason: values off A^m are never used; the paper's per-valuation map q_v is the record's q
--   - encoding: real-valued identity with a Lebesgue integral over [0,∞) → ENNReal.ofReal of FD equals the sum of lower Lebesgue integrals over (0,∞) of ENNReal.ofReal of the integrand; reason: FD and the integrand are nonnegative; the integrand vanishes above the largest price, so the integrals are finite and the identities agree
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), SHA-256 d6ed330221fdb64a0d8f70c7d0abbd3346ee1cb8f9e101a745f7e1e57d35230e, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/30.pdf, printed p. 9 / PDF p. 11, Proposition 2.4

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Model

open MeasureTheory

namespace SingleSampleCombPI.XOS

/-- **Proposition 2.4** (Chawla–Dang, STOC 2027 submission #30, printed p. 9 / PDF p. 11).
Layer-cake representation of the free-disposal value, in either regime:
`FD(x_1, …, x_n) = ∑_j ∫_0^∞ min{1, ∑_i x_{i,j} 1[q_{i,j}(x_i) ≥ w]} dw`. -/
theorem proposition_2_4 (A : Regime) {n m : ℕ} (b : Fin n → Buyer m) (x : Fin n → Vec m)
    (hb : ∀ i, (b i).Valid A) (hx : ∀ i, InDom A (x i)) :
    ENNReal.ofReal (FD A b x) =
      ∑ j, ∫⁻ w in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (min 1 (∑ i, x i j * (if w ≤ (b i).q (x i) j then 1 else 0))) := by sorry

end SingleSampleCombPI.XOS
