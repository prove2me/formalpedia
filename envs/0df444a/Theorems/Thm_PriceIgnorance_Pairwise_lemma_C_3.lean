-- Prove2me | Theorems.Thm_PriceIgnorance_Pairwise_lemma_C_3
-- name    : PriceIgnorance.Pairwise.lemma_C_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:13:09.333044+00:00
-- url     : https://prove2.me/theorems/35a078a5-c766-49e7-97fc-9444b5c98051
-- title:
--   Lemma C.3 — $K$ masked triples of one $Z$: all pairwise independent, and each triple determines $Z$
-- statement:
--   Let $m\ge1$, let $Z$ be a random variable on $\mathbb Z_m$ with law $\nu$, and for $i=1,\dots,K$ let $X^{(i)}_1,X^{(i)}_2$ be i.i.d. uniform on $\mathbb Z_m$, independent across $i$ and of $Z$. Set
--   $$X^{(i)}_3=Z-\big(X^{(i)}_1+X^{(i)}_2\big)\pmod m .$$
--   Then:
--
--   1. the variables $Z,X^{(1)}_1,X^{(1)}_2,X^{(1)}_3,\dots,X^{(K)}_1,X^{(K)}_2,X^{(K)}_3$ are pairwise independent;
--   2. for every $i\in[K]$, $Z$ is determined by $X^{(i)}_1,X^{(i)}_2,X^{(i)}_3$: there is a function $g$ with $Z=g(X^{(i)}_1,X^{(i)}_2,X^{(i)}_3)$.
--
--   In Theorem 3.19 the many triples make it likely that one complete triple, and hence the hidden sample $Z$, is seen before the values of interest under a random order.
--
--   Differences from the source:
--   - encoding: a random variable Z ∈ Z_m and masks independent of Z → the explicit space Z_m × (Z_m × Z_m)^K with law ν ⊗ (Uni ⊗ Uni)^{⊗K}, Z the first coordinate; reason: the construction fixes the joint law given the law ν of Z
--   - encoding: Z_m with Uni(Z_m) → ZMod m with 1 ≤ m; reason: Uni(Z_m) exists only for m ≥ 1 (Z_0 = Z has no uniform law)
--   - encoding: pairwise independence of Z_m-valued variables Z, X(1)_1, …, X(K)_3 → KWiseIndep with k = 2 of their images under x ↦ (x.val : ℝ), indexed by Fin (K·3 + 1) (0 = Z); reason: the embedding is injective, so independence is unchanged
--   - encoding: Z is determined by X(i)_1, X(i)_2, X(i)_3 → ∃ g, Z(ω) = g(X(i)_1(ω), X(i)_2(ω), X(i)_3(ω)) for every ω; reason: pointwise determination; Z = X1 + X2 + X3 holds everywhere
-- source:
--   Abdallah, Wajc, Price of Ignorance in Pairwise-Independent Prophet Inequalities, STOC 2027 submission (manuscript sha256 c79626fd…), p. 30, Lemma C.3

import Mathlib
import Definitions.Def_LaconicBarrier_KWiseIndep
import Definitions.Def_PriceIgnorance_Pairwise_ModMask

open MeasureTheory

namespace PriceIgnorance.Pairwise

/-- Lemma C.3 (p. 30): let `Z ∼ ν` on `ℤ_m` and, for `i = 1, …, K`, let `X^{(i)}_1, X^{(i)}_2` be
i.i.d. uniform on `ℤ_m`, independently across `i` and of `Z`, and
`X^{(i)}_3 = Z − (X^{(i)}_1 + X^{(i)}_2) mod m`. Then `Z, X^{(1)}_1, …, X^{(K)}_3` are pairwise
independent, and `Z` is determined by `X^{(i)}_1, X^{(i)}_2, X^{(i)}_3` for every `i`. -/
theorem lemma_C_3 (m K : ℕ) (hm : 1 ≤ m) (ν : Measure (ZMod m)) [IsProbabilityMeasure ν] :
    LaconicBarrier.KWiseIndep (tripleLaw m K ν) (fun t ω => zr (tripleFamily m K t ω)) 2 ∧
    ∀ i : Fin K, ∃ g : ZMod m × ZMod m × ZMod m → ZMod m,
      ∀ ω, ω.1 = g (tripleVar m K i 0 ω, tripleVar m K i 1 ω, tripleVar m K i 2 ω) := by sorry

end PriceIgnorance.Pairwise
