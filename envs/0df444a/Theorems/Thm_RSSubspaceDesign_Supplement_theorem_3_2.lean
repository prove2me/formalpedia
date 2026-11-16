-- Prove2me | Theorems.Thm_RSSubspaceDesign_Supplement_theorem_3_2
-- name    : RSSubspaceDesign.Supplement.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:38:39.63888+00:00
-- url     : https://prove2.me/theorems/8ad1be6e-12b9-4e47-a1ba-a48c6c90b08a
-- title:
--   Theorem 3.2 — capacity list recovery: $(1-R-\varepsilon, \ell, \lceil(\ell/(R+\varepsilon/2))^{3+2R/\varepsilon}\rceil)$
-- statement:
--   Fix $0 < R < 1$, $0 < \varepsilon < 1 - R$ and an integer $\ell \ge 2$, and put
--
--   $$
--   r = \Bigl\lceil \frac{2\ell}{\varepsilon} \Bigr\rceil, \qquad L = \Bigl\lceil \Bigl(\frac{\ell}{R + \varepsilon/2}\Bigr)^{3 + 2R/\varepsilon} \Bigr\rceil .
--   $$
--
--   Let $n$ be sufficiently large, $K$ a finite field with $|K| \ge n$, and let $F \supseteq K$ and distinct points $A = (\alpha_1, \dots, \alpha_n) \in F^n$ be as supplied by Theorem 1.1 with parameters $r, \varepsilon$. Concretely, $C = \mathrm{RS}_F(A, \lfloor Rn \rfloor)$ is a $\tau$-subspace-design code over $K$ for
--   $$
--   \tau(d) = \min\{1,\ \lfloor Rn\rfloor/n + \varepsilon/4\} \ (d \le r), \qquad \tau(d) = 1 \ (d > r).
--   $$
--   Then $C$ is $(1 - R - \varepsilon, \ell, L)$-list-recoverable: for any lists $S_1, \dots, S_n \subseteq F$ of size at most $\ell$, at most $L$ codewords fall outside the lists in at most $(1 - R - \varepsilon)n$ coordinates.
--
--   The list size depends only on $R$, $\varepsilon$ and $\ell$, not on $n$. This is list recovery at capacity for explicit Reed–Solomon codes.
--
--   **Formalization Note** "Supplied by Theorem 1.1" is the subspace-design property that Theorem 1.1 gives, assumed directly. The threshold for $n$ is chosen after $R, \varepsilon, \ell$ and before $n, K, F, A$. Ceilings are natural-number ceilings and the exponent is a real power.
--
--   Differences from the source:
--   - generalization: F, A supplied by Theorem 1.1 with parameters r, ε → any finite field F ⊇ K and distinct points α with RS_F(α, ⌊Rn⌋) a τ-subspace-design code over K for Theorem 1.1's τ (min{1, ⌊Rn⌋/n + ε/4} for d ≤ r, 1 for d > r); reason: Theorem 1.1 gives every output exactly this property (its conclusion at k = ⌊Rn⌋), so the Lean statement specializes to the source's
--   - encoding: n sufficiently large in the fixed parameters (Section 3 preamble, p.16) → a threshold N chosen after the fixed parameters and before n, K, F, α; reason: the standing assumption of Section 3, written out
-- source:
--   Alrabiah–Goyal–Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…f36206), Theorem 3.2, p.16 (PDF 18); standing assumption of Section 3, p.16

import Mathlib
import Definitions.Def_Yukon_e9ee7c0e88307b8acac3260e
import Definitions.Def_RSSubspaceDesign_IsSubspaceDesign
import Definitions.Def_RSSubspaceDesign_Supplement_IsListRecoverable

namespace RSSubspaceDesign

namespace Supplement

/-- **Theorem 3.2 (Capacity list recovery).** Alrabiah–Goyal–Guruswami, *Explicit Reed-Solomon
Subspace Designs: Optimal List and Line Decoding*, arXiv:2610.36215 (held version, sha256
cf26424b…f36206), Theorem 3.2, p.16 (standing assumption of Section 3, p.16: `n` sufficiently
large in the fixed parameters, `K` a finite field with `|K| ≥ n`).

Fix `0 < R < 1`, `0 < ε < 1 − R` and an integer `ℓ ≥ 2`, and let `r = ⌈2ℓ/ε⌉`,
`L = ⌈(ℓ/(R + ε/2))^{3 + 2R/ε}⌉`. Let `F, A` be supplied by Theorem 1.1 with parameters `r, ε`,
and put `C = RS_F(A, ⌊Rn⌋)`. Then `C` is `(1 − R − ε, ℓ, L)`-list-recoverable.

**Formalization Note.** "`F, A` supplied by Theorem 1.1 with parameters `r, ε`" is read as the
property Theorem 1.1 gives them: `K` a finite field with `n ≤ |K|`, `F` a finite field extending
`K`, distinct points `α : Fin n ↪ F`, and `RS_F(α, k)` (for `k = ⌊Rn⌋`) a `τ`-subspace-design code
over `K` with `τ(d) = min{1, k/n + ε/4}` for `d ≤ r` and `τ(d) = 1` for `d > r` (Theorem 1.1's
`τ` at rate `k/n`). Every output of Theorem 1.1 has this property, so the statement covers the
paper's. "`n` sufficiently large" is a threshold `N` chosen after `R, ε, ℓ` and before
`n, K, F, α`. Ceilings are `Nat.ceil`; the exponent is a real power. -/
theorem theorem_3_2 :
    ∀ R ε : ℝ, 0 < R → R < 1 → 0 < ε → ε < 1 - R → ∀ ℓ : ℕ, 2 ≤ ℓ →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ (K F : Type) [Field K] [Fintype K] [Field F] [Fintype F] [Algebra K F],
          n ≤ Fintype.card K → ∀ α : Fin n ↪ F,
          IsSubspaceDesign K ((ReedSolomon.code α ⌊R * n⌋₊).restrictScalars K)
              (fun d => if d ≤ ⌈2 * ℓ / ε⌉₊ then min 1 ((⌊R * n⌋₊ : ℝ) / n + ε / 4) else 1) →
            IsListRecoverable (ReedSolomon.code α ⌊R * n⌋₊ : Set (Fin n → F)) (1 - R - ε) ℓ
              ⌈((ℓ : ℝ) / (R + ε / 2)) ^ (3 + 2 * R / ε)⌉₊ := by sorry

end Supplement

end RSSubspaceDesign
