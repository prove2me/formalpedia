-- Prove2me | Theorems.Thm_TrapdoorHCF_CCA2_Supplement_lemma_11
-- name    : TrapdoorHCF.CCA2.Supplement.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:48:06.530115+00:00
-- url     : https://prove2.me/theorems/15c28273-0833-4b75-b12b-b74301072c35
-- title:
--   Lemma 11 — pairwise closeness implies near-independence
-- statement:
--   Let $\mathcal M$ be a finite nonempty set, let $\Omega$ be any set, and let $\{D_m\}_{m\in\mathcal M}$ be probability distributions on $\Omega$ with $\Delta(D_m,D_{m'})\le\varepsilon$ for all $m,m'\in\mathcal M$. Let $M,U$ be independent and uniform on $\mathcal M$, and let $C\leftarrow D_M$. Then
--
--   $$\Delta\bigl((C,M),\ (C,U)\bigr)\le\varepsilon.$$
--
--   The statement has no security parameter. Lemma 12 applies it to the ciphertext distributions of a lossy public key.
--
--   Differences from the source:
--   - reading: (C, M) ≈s (C, U) → Delta((C, M), (C, U)) <= epsilon with the same epsilon; reason: the lemma has no security parameter; this is the last display of its proof (p.52) and the form Lemma 12 quotes ("More precisely, Delta((C,M),(C,U)) <= epsilon(lambda)")
--   - encoding: a finite family of distributions and uniform M, U → a Fintype, Nonempty index type with PMF.uniformOfFintype; reason: a uniform label on an empty family is undefined, so nonemptiness only excludes an undefined case
--   - encoding: statistical distance (1/2) sum over omega of |Pr[X = omega] - Pr[Y = omega]| → (1/2) times the real tsum over all outcomes of |p(omega) - q(omega)| for PMFs on an arbitrary type; reason: the series is absolutely summable for PMFs, so this is the same number; no finiteness of the outcome space is assumed
-- source:
--   Kanad Chakravarti, Shreyas Gupta, Bhavana Kanukurthi, Girisha Shankar, Trapdoors Beyond Inversion: Recoverable Information in Public-Key Cryptography, STOC 2027 submission #571 (October 2026; unrefereed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/571.pdf, Lemma 11, p.51 (proof pp.51–52)

import Mathlib
import Definitions.Def_TrapdoorHCF_CCA2_Supplement_CPA
open QAlgorithms.Complexity
set_option autoImplicit false

namespace TrapdoorHCF.CCA2.Supplement

open TrapdoorHCF.CCA2

/-- Lemma 11, pp.51–52: for a finite nonempty family `{D_m}` with pairwise distance at most `ε`,
`M, U` independent uniform labels and `C ← D_M`, `Δ((C,M), (C,U)) ≤ ε` (p.52, last display). -/
theorem lemma_11 {ι α : Type} [Fintype ι] [Nonempty ι] (D : ι → PMF α) (ε : ℝ)
    (hD : ∀ m m' : ι, sd (D m) (D m') ≤ ε) :
    sd ((PMF.uniformOfFintype ι).bind fun m => (D m).map fun c => (c, m))
      (((PMF.uniformOfFintype ι).bind D).bind fun c =>
        (PMF.uniformOfFintype ι).map fun u => (c, u)) ≤ ε := by sorry

end TrapdoorHCF.CCA2.Supplement
