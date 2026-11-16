-- Prove2me | Theorems.Thm_TarskiQuasiFPT_UpperBound_Supplement_lemma_15
-- name    : TarskiQuasiFPT.UpperBound.Supplement.lemma_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:30:50.348279+00:00
-- url     : https://prove2.me/theorems/d21184dd-3534-4694-aaf0-71d76a2707e0
-- title:
--   Lemma 15 — every $F\in\operatorname{supp}(\mathrm{Amp}_m(\mathcal H))$ has the unique fixed point $(t^*,t^*,P^*,P^*)$
-- statement:
--   This is the §3.2 setting. $\mathcal H$ is a distribution whose support consists of monotone maps $H:[n]^k\to[n]^k$, each with a unique fixed point. Let $F\in\operatorname{supp}(\mathrm{Amp}_m(\mathcal H))$ come from the sampled functions $H_1,\dots,H_m\in\operatorname{supp}(\mathcal H)$, whose fixed points are $P_1,\dots,P_m\in[n]^k$, and from the hidden number $t^*\in[m]$. Let
--   $$P^*=\big(P_{t^*}+(t^*-1)n\mathbf 1,\ \overline{P_{t^*}}+(t^*-1)n\mathbf 1\big)\in[mn]^{2k}.$$
--   Then $F$ has the unique fixed point $(t^*,t^*,P^*,P^*)$. That is, for every $W\in[m]^2\times[mn]^{4k}$,
--   $$F(W)=W\iff W=(t^*,t^*,P^*,P^*).$$
--
--   The lemma ties the fixed point of the amplified instance to the hidden number $t^*$, so finding the fixed point requires learning $t^*$. Lemma 17 uses this.
--
--   **Formalization Note** The statement is made for every sample $(H_1,\dots,H_m,t^*)$ with each $H_t$ in the support of $\mathcal H$, and $F$ is the amplified function built from that sample. Each $P_t$ is given with $H_t(P_t)=P_t$; it is the unique fixed point because $H_t$ lies in the support. $P^*$ is the image of $(P_{t^*},\overline{P_{t^*}})$ in the box $B_{t^*}$. Indices are 0-based.
--
--   Differences from the source:
--   - encoding: [n] = {1,…,n}, points of [n]^k ordered coordinatewise → Point n k = Fin k → Fin n (0-based values) with the pointwise order; reason: shift by one; same order, same instances
--   - encoding: [m]^2 × [mn]^{4k} with W = (a, b, X, Y), ordered coordinatewise → AmpPoint m n k = Fin m × Fin m × (Point (m*n) k × Point (m*n) k) × (Point (m*n) k × Point (m*n) k) with the product order; reason: the product order is the coordinatewise order of the concatenated vector; 0-based values
--   - encoding: S_{H,c}(X) = c at X = (P_H, P̄_H) → signFn returns c when H X.1 = X.1 and X.2 = complement X.1; reason: identical point when H has a unique fixed point P_H, which every H in the support has (§3.2 setting)
--   - encoding: F ∈ supp(Amp_m(H)) with its sampled H_1..H_m and t* → ampFun Hs tstar for every Hs with Hs t ∈ D.support and every tstar : Fin m; reason: the support of Amp_m(H) is exactly the set of such ampFun Hs tstar, and the lemma names the sample
-- source:
--   Chen, Gao, Li, Rubinstein, Yannakakis, Tarski Fixed Points in Quasi-FPT Queries, STOC 2027 submission #403 (October 2026), SHA-256 6a2841836f544481cc4548db5ea0222917f43c713b7a292c9947be9c149b9cd6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/403.pdf, Lemma 15, PDF p. 20 (printed p. 19); construction §3.2.4, PDF pp. 18–20

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_TarskiQuasiFPT_UpperBound_Grid
import Definitions.Def_TarskiQuasiFPT_UpperBound_Supplement_LowerBound

open QAlgorithms
set_option autoImplicit false

namespace TarskiQuasiFPT.UpperBound.Supplement

/-- Lemma 15, PDF p. 20. §3.2 setting: `D` is a distribution whose support consists of monotone
maps `[n]^k → [n]^k` with a unique fixed point. Let `H_1, …, H_m` be sampled functions (in the
support of `D`) with unique fixed points `P_1, …, P_m`, and `t* ∈ [m]` the hidden number. With
`P* = (P_{t*} + (t*−1)n·1, \overline{P_{t*}} + (t*−1)n·1)`, the amplified function
`F = ampFun (H_1,…,H_m) t*` has the unique fixed point `(t*, t*, P*, P*)`. -/
theorem lemma_15 {n k m : ℕ} (D : PMF (Point n k → Point n k))
    (hD : ∀ H ∈ D.support, Monotone H ∧ HasUniqueFixedPoint H)
    (Hs : Fin m → Point n k → Point n k) (hHs : ∀ t, Hs t ∈ D.support)
    (P : Fin m → Point n k) (hP : ∀ t, Hs t (P t) = P t) (tstar : Fin m) :
    ∀ W : AmpPoint m n k, ampFun Hs tstar W = W ↔
      W = (tstar, tstar, toGlobal tstar (P tstar, complement (P tstar)),
        toGlobal tstar (P tstar, complement (P tstar))) := by sorry

end TarskiQuasiFPT.UpperBound.Supplement
