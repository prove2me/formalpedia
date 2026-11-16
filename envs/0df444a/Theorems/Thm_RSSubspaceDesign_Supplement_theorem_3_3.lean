-- Prove2me | Theorems.Thm_RSSubspaceDesign_Supplement_theorem_3_3
-- name    : RSSubspaceDesign.Supplement.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:39:28.327079+00:00
-- url     : https://prove2.me/theorems/5f44fa27-a84b-4b4b-b455-8e49d71d1613
-- title:
--   Theorem 3.3 — base-field capacity curve decoding: $(\ell, 1-R-\varepsilon, a_0, b_0)$-$K$-curve-decodable
-- statement:
--   Fix $0 < R < 1$, $0 < \varepsilon < 1 - R$ and an integer $\ell \ge 1$, and set
--
--   $$
--   b_0 = \ell + \Bigl\lceil \frac{8(\ell+1)}{\varepsilon} \Bigr\rceil, \qquad r = \Bigl\lceil \frac{8(\ell+1)}{\varepsilon} \Bigr\rceil, \qquad a_0 = \Bigl\lceil \frac{2 b_0 (r + \varepsilon/2)}{\varepsilon} \Bigr\rceil .
--   $$
--
--   Let $n$ be sufficiently large, $K$ a finite field with $|K| \ge n$, and let $F$, $A$ be supplied by Theorem 1.1 with parameters $r, \varepsilon$: $C = \mathrm{RS}_F(A, \lfloor Rn \rfloor)$ is a $\tau$-subspace-design code over $K$ with $\tau(d) = \min\{1, \lfloor Rn\rfloor/n + \varepsilon/4\}$ for $d \le r$ and $\tau(d) = 1$ for $d > r$. Then $C$, viewed as a $K$-linear code, is $(\ell, 1 - R - \varepsilon, a_0, b_0)$-$K$-curve-decodable. Whenever at least $a_0$ parameters $\alpha \in K$ of a degree-$\ell$ curve $\sum_j u_j \alpha^j$ are within relative distance $1 - R - \varepsilon$ of assigned codewords $f(\alpha)$, at least $b_0$ of those codewords lie on one degree-$\ell$ curve of codewords.
--
--   **Formalization Note** "Supplied by Theorem 1.1" is assumed as the subspace-design property; $n$ is beyond a threshold chosen after $R, \varepsilon, \ell$. The parameter $L = \lceil 8/\varepsilon\rceil$ that the theorem also sets does not occur in its conclusion. Curves are parameterized by $\alpha \in K$, acting on $F^n$ through $K \subseteq F$.
--
--   Differences from the source:
--   - generalization: F, A supplied by Theorem 1.1 with parameters r, ε → any finite field F ⊇ K and distinct points α with RS_F(α, ⌊Rn⌋) a τ-subspace-design code over K for Theorem 1.1's τ (min{1, ⌊Rn⌋/n + ε/4} for d ≤ r, 1 for d > r); reason: Theorem 1.1 gives every output exactly this property (its conclusion at k = ⌊Rn⌋), so the Lean statement specializes to the source's
--   - encoding: n sufficiently large in the fixed parameters (Section 3 preamble, p.16) → a threshold N chosen after the fixed parameters and before n, K, F, α; reason: the standing assumption of Section 3, written out
--   - encoding: "Set L = ⌈8/ε⌉" → L is not written; reason: L does not occur in the conclusion of Theorem 3.3
-- source:
--   Alrabiah–Goyal–Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…f36206), Theorem 3.3, pp.16–17 (PDF 18–19); standing assumption of Section 3, p.16

import Mathlib
import Definitions.Def_Yukon_e9ee7c0e88307b8acac3260e
import Definitions.Def_RSSubspaceDesign_IsSubspaceDesign
import Definitions.Def_RSSubspaceDesign_Supplement_IsCurveDecodable

namespace RSSubspaceDesign

namespace Supplement

/-- **Theorem 3.3 (Base-field capacity curve decoding).** Alrabiah–Goyal–Guruswami,
arXiv:2610.36215 (held version, sha256 cf26424b…f36206), Theorem 3.3, pp.16–17 (standing
assumption of Section 3, p.16: `n` sufficiently large in the fixed parameters, `K` a finite field
with `|K| ≥ n`).

Fix `0 < R < 1`, `0 < ε < 1 − R` and an integer `ℓ ≥ 1`. Set `L = ⌈8/ε⌉`,
`b₀ = ℓ + ⌈8(ℓ + 1)/ε⌉`, `r = ⌈8(ℓ + 1)/ε⌉`, `a₀ = ⌈2b₀(r + ε/2)/ε⌉`. Let `F, A` be supplied by
Theorem 1.1 with parameters `r, ε`, and put `C = RS_F(A, ⌊Rn⌋)`. Then `C` is
`(ℓ, 1 − R − ε, a₀, b₀)`-`K`-curve-decodable.

**Formalization Note.** "`F, A` supplied by Theorem 1.1" is read as in `theorem_3_2`: `K` finite
with `n ≤ |K|`, `F` a finite extension, distinct points, and `RS_F(α, ⌊Rn⌋)` a `τ`-subspace-design
code over `K` with Theorem 1.1's `τ` for this `r`. `N` is chosen after `R, ε, ℓ`. `L` does not
occur in the conclusion and is not written. `K`-curve decodability is `IsCurveDecodable K` of the
code viewed as a `K`-subspace (`restrictScalars`), `α ∈ K` acting on `Fⁿ` through `K → F`. -/
theorem theorem_3_3 :
    ∀ R ε : ℝ, 0 < R → R < 1 → 0 < ε → ε < 1 - R → ∀ ℓ : ℕ, 1 ≤ ℓ →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ (K F : Type) [Field K] [Fintype K] [Field F] [Fintype F] [Algebra K F],
          n ≤ Fintype.card K → ∀ α : Fin n ↪ F,
          IsSubspaceDesign K ((ReedSolomon.code α ⌊R * n⌋₊).restrictScalars K)
              (fun d => if d ≤ ⌈8 * ((ℓ : ℝ) + 1) / ε⌉₊ then min 1 ((⌊R * n⌋₊ : ℝ) / n + ε / 4)
                else 1) →
            IsCurveDecodable K ((ReedSolomon.code α ⌊R * n⌋₊).restrictScalars K) ℓ (1 - R - ε)
              ⌈2 * ((ℓ + ⌈8 * ((ℓ : ℝ) + 1) / ε⌉₊ : ℕ) : ℝ) *
                  ((⌈8 * ((ℓ : ℝ) + 1) / ε⌉₊ : ℝ) + ε / 2) / ε⌉₊
              ((ℓ + ⌈8 * ((ℓ : ℝ) + 1) / ε⌉₊ : ℕ) : ℝ) := by sorry

end Supplement

end RSSubspaceDesign
