-- Prove2me | Theorems.Thm_RSSubspaceDesign_Supplement_theorem_3_5
-- name    : RSSubspaceDesign.Supplement.theorem_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:40:48.224651+00:00
-- url     : https://prove2.me/theorems/318f8e3b-c5a1-4fb7-9566-31ca074ca411
-- title:
--   Theorem 3.5 — capacity line decoding: $(1, 1-R-\varepsilon, (t-1)L+\lceil|F|a_0/|K|\rceil, t)$-$F$-curve-decodable for every $t \ge 1$
-- statement:
--   Fix $0 < R < 1$ and $0 < \varepsilon < 1 - R$, and set
--
--   $$
--   L = \Bigl\lceil \frac{8}{\varepsilon} \Bigr\rceil,\quad r = \Bigl\lceil \frac{16}{\varepsilon} \Bigr\rceil,\quad b_0 = 1 + \Bigl\lceil \frac{16}{\varepsilon} \Bigr\rceil,\quad a_0 = \Bigl\lceil \frac{2 b_0 (r + \varepsilon/2)}{\varepsilon} \Bigr\rceil .
--   $$
--
--   Let $n$ be sufficiently large, $K$ a finite field with $|K| \ge n$, and $F$, $A$ supplied by Theorem 1.1 with parameters $r, \varepsilon$ (so $C = \mathrm{RS}_F(A, \lfloor Rn\rfloor)$ is a $\tau$-subspace-design code over $K$ with Theorem 1.1's $\tau$). Then for every integer $t \ge 1$, $C$ is
--
--   $$
--   \bigl(1,\ 1 - R - \varepsilon,\ (t-1)L + \lceil |F| a_0 / |K| \rceil,\ t\bigr)\text{-}F\text{-curve-decodable},
--   $$
--
--   that is, line-decodable over the extension field.
--
--   **Formalization Note** "Supplied by Theorem 1.1" is assumed as the subspace-design property; $n$ is beyond a threshold chosen after $R, \varepsilon$. $|F| a_0/|K|$ is a real quotient and $(t-1)L$ a natural number. No size condition on $F$ is assumed, as in the printed statement.
--
--   Differences from the source:
--   - generalization: F, A supplied by Theorem 1.1 with parameters r, ε → any finite field F ⊇ K and distinct points α with RS_F(α, ⌊Rn⌋) a τ-subspace-design code over K for Theorem 1.1's τ (min{1, ⌊Rn⌋/n + ε/4} for d ≤ r, 1 for d > r); reason: Theorem 1.1 gives every output exactly this property (its conclusion at k = ⌊Rn⌋), so the Lean statement specializes to the source's
--   - encoding: n sufficiently large in the fixed parameters (Section 3 preamble, p.16) → a threshold N chosen after the fixed parameters and before n, K, F, α; reason: the standing assumption of Section 3, written out
-- source:
--   Alrabiah–Goyal–Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…f36206), Theorem 3.5, p.17 (PDF 19); standing assumption of Section 3, p.16

import Mathlib
import Definitions.Def_Yukon_e9ee7c0e88307b8acac3260e
import Definitions.Def_RSSubspaceDesign_IsSubspaceDesign
import Definitions.Def_RSSubspaceDesign_Supplement_IsCurveDecodable

namespace RSSubspaceDesign

namespace Supplement

/-- **Theorem 3.5 (Capacity line decoding).** Alrabiah–Goyal–Guruswami, arXiv:2610.36215 (held
version, sha256 cf26424b…f36206), Theorem 3.5, p.17 (standing assumption of Section 3, p.16:
`n` sufficiently large in the fixed parameters, `K` a finite field with `|K| ≥ n`).

Fix `0 < R < 1` and `0 < ε < 1 − R`. Set `L = ⌈8/ε⌉`, `r = ⌈16/ε⌉`, `b₀ = 1 + ⌈16/ε⌉`,
`a₀ = ⌈2b₀(r + ε/2)/ε⌉`. Let `F, A` be supplied by Theorem 1.1 with parameters `r, ε`, and put
`C = RS_F(A, ⌊Rn⌋)`. Then, for every integer `t ≥ 1`, `C` is
`(1, 1 − R − ε, (t − 1)L + ⌈|F|a₀/|K|⌉, t)`-`F`-curve-decodable.

**Formalization Note.** "`F, A` supplied by Theorem 1.1" is read as in `theorem_3_2` (`τ` with
`r = ⌈16/ε⌉`); `N` is chosen after `R, ε`. `|F|a₀/|K|` is a real quotient; `(t − 1)L` is a natural
number (`t ≥ 1`). -/
theorem theorem_3_5 :
    ∀ R ε : ℝ, 0 < R → R < 1 → 0 < ε → ε < 1 - R →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ (K F : Type) [Field K] [Fintype K] [Field F] [Fintype F] [Algebra K F],
          n ≤ Fintype.card K → ∀ α : Fin n ↪ F,
          IsSubspaceDesign K ((ReedSolomon.code α ⌊R * n⌋₊).restrictScalars K)
              (fun d => if d ≤ ⌈16 / ε⌉₊ then min 1 ((⌊R * n⌋₊ : ℝ) / n + ε / 4) else 1) →
          ∀ t : ℕ, 1 ≤ t →
            IsCurveDecodable F (ReedSolomon.code α ⌊R * n⌋₊) 1 (1 - R - ε)
              ((t - 1) * ⌈8 / ε⌉₊ +
                ⌈(Fintype.card F : ℝ) *
                  (⌈2 * ((1 + ⌈16 / ε⌉₊ : ℕ) : ℝ) * ((⌈16 / ε⌉₊ : ℝ) + ε / 2) / ε⌉₊ : ℝ) /
                    Fintype.card K⌉₊)
              t := by sorry

end Supplement

end RSSubspaceDesign
