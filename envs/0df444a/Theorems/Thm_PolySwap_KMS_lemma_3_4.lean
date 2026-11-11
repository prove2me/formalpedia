-- Prove2me | Theorems.Thm_PolySwap_KMS_lemma_3_4
-- name    : PolySwap.KMS.lemma_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:42:00.271208+00:00
-- url     : https://prove2.me/theorems/402332f9-d60c-4095-ac6a-899f17c288cf
-- title:
--   Lemma 3.4 — $F^r(X^{\le n})$ is a $\gamma_1$-local spectral expander when $d\ge n+\frac{r+1}{\gamma_1}+1$ and $q>16$
-- statement:
--   Let $r,n,d\in\mathbb N$ satisfy $2r+1\le n\le d$, and let $\gamma_1\in(0,1)$. Suppose that
--   $$d\ge n+\frac{r+1}{\gamma_1}+1.$$
--   For every prime power $q>16$ and every irreducible $f\in\mathbb F_q[t]$ of degree at least two, the complex $F^r(X^{\le n})$, where $X=X(A_d,\mathbb F_q,f)$, is a $\gamma_1$-local spectral expander. The skeleton carries the weights inherited from $X$ (p. 11).
--
--   Differences from the source:
--   - encoding: r ∈ ℕ (the paper's ℕ excludes 0: it writes ℕ₀ for {0, 1, …}, p. 9; Definitions 2.11 and 2.14 assume 1 ≤ r) → hypothesis 1 ≤ r; reason: the paper's standing convention made explicit
--   - encoding: a prime power q = p^m and the field F_q → a finite field F (Fintype F) with q = Fintype.card F and p = ringChar F; reason: every finite field has prime-power order q and prime characteristic p; same instances
--   - encoding: X(A_d, F_q, f) = CC(SL_{d+1}(F_q[t]/(f)); (π_f(U_{[d]∖{i}}))_{i∈[d]}) with the uniform top-level distribution → kmsX d F f: cosetComplex over SL (Fin (d+1)) (AdjoinRoot f) of Hf d F f i = (U d F ([d]∖{i})).map (SpecialLinearGroup.map (AdjoinRoot.mk f)), vertices ⟨i, gH^f_i⟩ : Σ i, G ⧸ H^f_i, colour i; reason: Lean convention (0-based matrix indices, F_q[t]/(f) as AdjoinRoot f); the same complex and weights
--   - encoding: λ₂ ≤ γ₁ on every link (Definition 2.7) → IsLocalSpectralExpander (variational form); reason: Courant–Fischer; equivalent
--   - encoding: X^{≤n} with the top-level distribution w_n inherited from X → skeleton n: maximal faces the faces of X with n + 1 vertices, weighted by the Garland weight gw of X; reason: the convention of p. 11
-- source:
--   Dikstein, Oppenheim, Valentiner-Branth, Polynomial Swap Coboundary Expansion with Applications to LTCs and PCPs, STOC 2027 submission (manuscript sha256 b9cb2095…), Lemma 3.4, pp. 22–23

import Mathlib
import Definitions.Def_PolySwap_KMS_Complex
import Definitions.Def_PolySwap_KMS_Dehn
import Definitions.Def_PolySwap_KMS_KMSComplex

open Polynomial

namespace PolySwap.KMS

/-- **Lemma 3.4**, pp. 22–23. Let `r, n, d ∈ ℕ` with `2r + 1 ≤ n ≤ d`, let `γ₁ ∈ (0, 1)` and
suppose `d ≥ n + (r + 1)/γ₁ + 1`. For every prime power `q > 16` and every irreducible
`f ∈ F_q[t]` of degree at least two, `F^r(X^{≤n})`, `X = X(A_d, F_q, f)`, is a `γ₁`-local
spectral expander (the skeleton carries the weights inherited from `X`). -/
theorem lemma_3_4 (r n d : ℕ) (hr : 1 ≤ r) (hrn : 2 * r + 1 ≤ n) (hnd : n ≤ d)
    (γ₁ : ℝ) (hγ₀ : 0 < γ₁) (hγ₁ : γ₁ < 1) (hd : (n : ℝ) + (r + 1) / γ₁ + 1 ≤ d)
    (F : Type*) [Field F] [Fintype F] (hq : 16 < Fintype.card F)
    (f : F[X]) (hf : Irreducible f) (hdeg : 2 ≤ f.natDegree) :
    (((kmsX d F f).skeleton n).facesComplex r).IsLocalSpectralExpander γ₁ := by sorry

end PolySwap.KMS
