-- Prove2me | Theorems.Thm_TarskiQuasiFPT_UpperBound_Supplement_lemma_16
-- name    : TarskiQuasiFPT.UpperBound.Supplement.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:31:24.483081+00:00
-- url     : https://prove2.me/theorems/a73f9993-859d-4a7e-81ec-20a323e7bb58
-- title:
--   Lemma 16 — every $F\in\operatorname{supp}(\mathrm{Amp}_m(\mathcal H))$ is monotone
-- statement:
--   This is the §3.2 setting. $\mathcal H$ is a distribution whose support consists of monotone maps $H:[n]^k\to[n]^k$, each with a unique fixed point, and $m\ge1$. Then every member $F$ of the support of the amplified distribution $\mathrm{Amp}_m(\mathcal H)$ is monotone for the coordinatewise order on $[m]^2\times[mn]^{4k}$:
--   $$W\preceq W'\implies F(W)\preceq F(W').$$
--
--   Together with Lemma 15, this shows that each amplification step again produces a distribution of monotone functions with unique fixed points, which is what the induction in Theorem 6 needs.
--
--   **Formalization Note** The support is that of the `PMF` $\mathrm{Amp}_m(\mathcal H)$ defined in the definition file. The order on $[m]^2\times[mn]^{4k}$ is the product order, which is the coordinatewise order.
--
--   Differences from the source:
--   - encoding: [n] = {1,…,n}, points of [n]^k ordered coordinatewise → Point n k = Fin k → Fin n (0-based values) with the pointwise order; reason: shift by one; same order, same instances
--   - encoding: [m]^2 × [mn]^{4k} with W = (a, b, X, Y), ordered coordinatewise → AmpPoint m n k = Fin m × Fin m × (Point (m*n) k × Point (m*n) k) × (Point (m*n) k × Point (m*n) k) with the product order; reason: the product order is the coordinatewise order of the concatenated vector; 0-based values
--   - encoding: S_{H,c}(X) = c at X = (P_H, P̄_H) → signFn returns c when H X.1 = X.1 and X.2 = complement X.1; reason: identical point when H has a unique fixed point P_H, which every H in the support has (§3.2 setting)
--   - encoding: m the base side-length of Amp_m, t* uniform on [m] → [NeZero m]; reason: uniform on [m] is undefined for m = 0; excludes only the undefined case
-- source:
--   Chen, Gao, Li, Rubinstein, Yannakakis, Tarski Fixed Points in Quasi-FPT Queries, STOC 2027 submission #403 (October 2026), SHA-256 6a2841836f544481cc4548db5ea0222917f43c713b7a292c9947be9c149b9cd6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/403.pdf, Lemma 16, PDF p. 21 (printed p. 20)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_TarskiQuasiFPT_UpperBound_Grid
import Definitions.Def_TarskiQuasiFPT_UpperBound_Supplement_LowerBound

open QAlgorithms
set_option autoImplicit false

namespace TarskiQuasiFPT.UpperBound.Supplement

/-- Lemma 16, PDF p. 21. §3.2 setting: `D` is a distribution whose support consists of monotone
maps `[n]^k → [n]^k` with a unique fixed point, and `m ≥ 1`. Every member of the support of
`Amp_m(D)` is monotone (for the coordinatewise order on `[m]^2 × [mn]^{4k}`). -/
theorem lemma_16 {n k m : ℕ} [NeZero m] (D : PMF (Point n k → Point n k))
    (hD : ∀ H ∈ D.support, Monotone H ∧ HasUniqueFixedPoint H) :
    ∀ F ∈ (ampDist m D).support, Monotone F := by sorry

end TarskiQuasiFPT.UpperBound.Supplement
