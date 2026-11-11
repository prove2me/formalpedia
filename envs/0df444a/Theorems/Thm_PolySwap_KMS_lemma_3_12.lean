-- Prove2me | Theorems.Thm_PolySwap_KMS_lemma_3_12
-- name    : PolySwap.KMS.lemma_3_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:41:38.441026+00:00
-- url     : https://prove2.me/theorems/c48e2d9c-b049-4016-b8ec-12ba2bdd9a15
-- title:
--   Lemma 3.12 — $F^{\mathcal I}X$ is a $\frac{2(r+1)}{\sqrt q-2}$-local spectral expander
-- statement:
--   Let $X=X(A_d,\mathbb F_q,f)$, where $q>16$ and $f$ is irreducible of degree at least two. Let $\mathcal I$ consist of $T\ge3$ pairwise disjoint colour sets, each of size $r+1$. Then $F^{\mathcal I}X$ is a $\frac{2(r+1)}{\sqrt q-2}$-local spectral expander.
--
--   Differences from the source:
--   - encoding: a prime power q = p^m and the field F_q → a finite field F (Fintype F) with q = Fintype.card F and p = ringChar F; reason: every finite field has prime-power order q and prime characteristic p; same instances
--   - encoding: X(A_d, F_q, f) = CC(SL_{d+1}(F_q[t]/(f)); (π_f(U_{[d]∖{i}}))_{i∈[d]}) with the uniform top-level distribution → kmsX d F f: cosetComplex over SL (Fin (d+1)) (AdjoinRoot f) of Hf d F f i = (U d F ([d]∖{i})).map (SpecialLinearGroup.map (AdjoinRoot.mk f)), vertices ⟨i, gH^f_i⟩ : Σ i, G ⧸ H^f_i, colour i; reason: Lean convention (0-based matrix indices, F_q[t]/(f) as AdjoinRoot f); the same complex and weights
--   - encoding: d ≥ 2 (§2.3) and 1 ≤ r (Definition 2.14); T ≥ 3 pairwise disjoint colour sets of size r + 1 in [d] → hypotheses 2 ≤ d, 1 ≤ r, 3 ≤ T and I ∈ disjointColorSets d r T; reason: the standing assumptions as binders
--   - encoding: λ₂ of the random walk on each weighted link 1-skeleton ≤ ε (Definition 2.7) → IsLocalSpectralExpander: the variational form of λ₂ ≤ ε on ℓ²(π); reason: Courant–Fischer for the self-adjoint walk; equivalent
-- source:
--   Dikstein, Oppenheim, Valentiner-Branth, Polynomial Swap Coboundary Expansion with Applications to LTCs and PCPs, STOC 2027 submission (manuscript sha256 b9cb2095…), Lemma 3.12, p. 26

import Mathlib
import Definitions.Def_PolySwap_KMS_Complex
import Definitions.Def_PolySwap_KMS_Dehn
import Definitions.Def_PolySwap_KMS_KMSComplex

open Polynomial

namespace PolySwap.KMS

/-- **Lemma 3.12**, p. 26. Let `X = X(A_d, F_q, f)` with `q > 16` and `f` irreducible of degree
at least two, and let `I` consist of `T ≥ 3` pairwise disjoint colour sets, each of size `r + 1`.
Then `F^I X` is a `2(r+1)/(√q − 2)`-local spectral expander. -/
theorem lemma_3_12 (d r T : ℕ) (hd : 2 ≤ d) (hr : 1 ≤ r) (hT : 3 ≤ T)
    (F : Type*) [Field F] [Fintype F] (hq : 16 < Fintype.card F)
    (f : F[X]) (hf : Irreducible f) (hdeg : 2 ≤ f.natDegree)
    (I : Finset (Finset ℕ)) (hI : I ∈ disjointColorSets d r T) :
    (kmsFI d F f I).IsLocalSpectralExpander
      (2 * (r + 1) / (Real.sqrt (Fintype.card F) - 2)) := by sorry

end PolySwap.KMS
