-- Prove2me | Theorems.Thm_RSSubspaceDesign_Supplement_theorem_3_4
-- name    : RSSubspaceDesign.Supplement.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:40:04.928202+00:00
-- url     : https://prove2.me/theorems/e1d5936e-4fc0-46f2-a990-35341743c0ec
-- title:
--   Theorem 3.4 — extension-field capacity curve decoding: $(\ell, 1-R-\varepsilon, (t-1)L+a_F, t)$-$F$-curve-decodable for every $t \ge 1$
-- statement:
--   Fix $0 < R < 1$, $0 < \varepsilon < 1 - R$ and an integer $\ell \ge 1$, and take the parameters of Theorem 3.3:
--
--   $$
--   L = \Bigl\lceil \frac{8}{\varepsilon} \Bigr\rceil,\quad b_0 = \ell + \Bigl\lceil \frac{8(\ell+1)}{\varepsilon} \Bigr\rceil,\quad r = \Bigl\lceil \frac{8(\ell+1)}{\varepsilon} \Bigr\rceil,\quad a_0 = \Bigl\lceil \frac{2 b_0 (r + \varepsilon/2)}{\varepsilon} \Bigr\rceil .
--   $$
--
--   Let $n$ be sufficiently large, $K$ a finite field with $|K| \ge n$, and $F$, $A$ supplied by Theorem 1.1 with parameters $r, \varepsilon$ (that is, $C = \mathrm{RS}_F(A, \lfloor Rn\rfloor)$ is a $\tau$-subspace-design code over $K$ with Theorem 1.1's $\tau$). Assume also $|F| > (L+1)^2 \ell$, and put
--
--   $$
--   a_F = \Bigl\lceil \frac{|F|}{|K|}\, a_0 \Bigr\rceil .
--   $$
--
--   Then for every integer $t \ge 1$ the code $C$ is $(\ell, 1 - R - \varepsilon, (t-1)L + a_F, t)$-$F$-curve-decodable: the curves are now parameterized by the extension field $F$.
--
--   **Formalization Note** "Supplied by Theorem 1.1" is assumed as the subspace-design property; $n$ is beyond a threshold chosen after $R, \varepsilon, \ell$. The size condition is $(L+1)^2\cdot\ell < |F|$, $|F|/|K|$ is a real quotient, and $(t-1)L$ is a natural number.
--
--   Differences from the source:
--   - generalization: F, A supplied by Theorem 1.1 with parameters r, ε → any finite field F ⊇ K and distinct points α with RS_F(α, ⌊Rn⌋) a τ-subspace-design code over K for Theorem 1.1's τ (min{1, ⌊Rn⌋/n + ε/4} for d ≤ r, 1 for d > r); reason: Theorem 1.1 gives every output exactly this property (its conclusion at k = ⌊Rn⌋), so the Lean statement specializes to the source's
--   - encoding: n sufficiently large in the fixed parameters (Section 3 preamble, p.16) → a threshold N chosen after the fixed parameters and before n, K, F, α; reason: the standing assumption of Section 3, written out
-- source:
--   Alrabiah–Goyal–Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…f36206), Theorem 3.4, p.17 (PDF 19), with the parameters of Theorem 3.3, pp.16–17; standing assumption of Section 3, p.16

import Mathlib
import Definitions.Def_Yukon_e9ee7c0e88307b8acac3260e
import Definitions.Def_RSSubspaceDesign_IsSubspaceDesign
import Definitions.Def_RSSubspaceDesign_Supplement_IsCurveDecodable

namespace RSSubspaceDesign

namespace Supplement

/-- **Theorem 3.4 (Extension-field capacity curve decoding).** Alrabiah–Goyal–Guruswami,
arXiv:2610.36215 (held version, sha256 cf26424b…f36206), Theorem 3.4, p.17, under the hypotheses
and parameter choices of Theorem 3.3, pp.16–17 (standing assumption of Section 3, p.16).

Fix `0 < R < 1`, `0 < ε < 1 − R`, an integer `ℓ ≥ 1`, and `L = ⌈8/ε⌉`, `b₀ = ℓ + ⌈8(ℓ + 1)/ε⌉`,
`r = ⌈8(ℓ + 1)/ε⌉`, `a₀ = ⌈2b₀(r + ε/2)/ε⌉`. Let `F, A` be supplied by Theorem 1.1 with parameters
`r, ε`, put `C = RS_F(A, ⌊Rn⌋)`, assume also `|F| > (L + 1)²ℓ`, and put `a_F = ⌈(|F|/|K|)a₀⌉`.
Then, for every integer `t ≥ 1`, `C` is `(ℓ, 1 − R − ε, (t − 1)L + a_F, t)`-`F`-curve-decodable.

**Formalization Note.** "`F, A` supplied by Theorem 1.1" is read as in `theorem_3_2` (`τ` with
Theorem 3.3's `r`); `N` is chosen after `R, ε, ℓ`. The size condition is `(L + 1)² · ℓ < |F|`
(the printed `(L + 1)²ℓ`, p.17). `|F|/|K|` is a real quotient; `(t − 1)L` is a natural number
(`t ≥ 1`). `F`-curve decodability is `IsCurveDecodable F` of the `F`-linear code. -/
theorem theorem_3_4 :
    ∀ R ε : ℝ, 0 < R → R < 1 → 0 < ε → ε < 1 - R → ∀ ℓ : ℕ, 1 ≤ ℓ →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ (K F : Type) [Field K] [Fintype K] [Field F] [Fintype F] [Algebra K F],
          n ≤ Fintype.card K → ∀ α : Fin n ↪ F,
          IsSubspaceDesign K ((ReedSolomon.code α ⌊R * n⌋₊).restrictScalars K)
              (fun d => if d ≤ ⌈8 * ((ℓ : ℝ) + 1) / ε⌉₊ then min 1 ((⌊R * n⌋₊ : ℝ) / n + ε / 4)
                else 1) →
          (⌈8 / ε⌉₊ + 1) ^ 2 * ℓ < Fintype.card F →
          ∀ t : ℕ, 1 ≤ t →
            IsCurveDecodable F (ReedSolomon.code α ⌊R * n⌋₊) ℓ (1 - R - ε)
              ((t - 1) * ⌈8 / ε⌉₊ +
                ⌈(Fintype.card F : ℝ) / Fintype.card K *
                  (⌈2 * ((ℓ + ⌈8 * ((ℓ : ℝ) + 1) / ε⌉₊ : ℕ) : ℝ) *
                    ((⌈8 * ((ℓ : ℝ) + 1) / ε⌉₊ : ℝ) + ε / 2) / ε⌉₊ : ℝ)⌉₊)
              t := by sorry

end Supplement

end RSSubspaceDesign
