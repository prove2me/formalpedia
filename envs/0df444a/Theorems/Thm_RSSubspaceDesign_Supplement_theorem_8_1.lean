-- Prove2me | Theorems.Thm_RSSubspaceDesign_Supplement_theorem_8_1
-- name    : RSSubspaceDesign.Supplement.theorem_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:44:28.999208+00:00
-- url     : https://prove2.me/theorems/b0989ac8-88ec-42c7-914d-a129e3c8775e
-- title:
--   Theorem 8.1 — line decoding over the extension field: $(1-\tau(D_a)-\varepsilon, a, a\varepsilon^2/4)$-$F$-line-decodable, $D_a=\lceil 2^{5a}/\varepsilon\rceil$
-- statement:
--   Let $K \subseteq F$ be finite fields, let $\Sigma$ be a finite-dimensional $F$-vector space, and let $C \subseteq \Sigma^n$ be an $F$-linear code. Suppose $C$ is a $\tau$-subspace-design code over $K$, for a nondecreasing $\tau : \mathbb Z_{\ge 1} \to [0,1]$. For an integer $a \ge 1$ and $0 < \varepsilon < 1$ set
--   $$
--   D_a = \Bigl\lceil \frac{2^{5a}}{\varepsilon} \Bigr\rceil .
--   $$
--   If $\tau(D_a) + \varepsilon \le 1$, then $C$ is
--   $$
--   \Bigl(1 - \tau(D_a) - \varepsilon,\ a,\ \frac{a\varepsilon^2}{4}\Bigr)\text{-}F\text{-line-decodable}.
--   $$
--
--   The subspace-design hypothesis is only over the subfield $K$, while the conclusion is about lines parameterized by the whole extension field $F$. This lift is what turns the subspace-design bound of Theorem 1.1 into the extension-field line decoding of Theorem 1.4.
--
--   **Formalization Note** $\Sigma$ is a $K$-vector space through $F$. "Subspace design over $K$" is the published `IsSubspaceDesign` applied to $C$ viewed as a $K$-subspace. That definition leaves $\tau$ arbitrary, so the conditions of Definition 2.1 on $\tau$ (values in $[0,1]$ and nondecreasing on $d \ge 1$) are explicit hypotheses here. $b = a\varepsilon^2/4$ is real.
--
--   Differences from the source:
--   - encoding: τ : ℤ≥1 → [0, 1] nondecreasing (the precondition of Definition 2.1) → τ : ℕ → ℝ with hypotheses 0 ≤ τ(d) ≤ 1 and monotonicity for d ≥ 1; reason: the published IsSubspaceDesign does not bundle the precondition; its value at 0 is never used
--   - encoding: K ⊆ F finite fields; Σ a finite-dimensional F-vector space; C an F-additive code → an algebra K → F of finite fields; Σ an F-module, finite-dimensional, a K-module through F (scalar tower); C an F-submodule of Σⁿ, viewed over K by restriction of scalars; reason: Lean's rendering of a field tower and an F-linear code
-- source:
--   Alrabiah–Goyal–Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…f36206), Theorem 8.1, p.42 (PDF 44)

import Mathlib
import Definitions.Def_RSSubspaceDesign_IsSubspaceDesign
import Definitions.Def_RSSubspaceDesign_Supplement_IsCurveDecodable

namespace RSSubspaceDesign

namespace Supplement

/-- **Theorem 8.1 (Line decoding over the extension field).** Alrabiah–Goyal–Guruswami,
arXiv:2610.36215 (held version, sha256 cf26424b…f36206), Theorem 8.1, p.42.

Let `K ⊆ F` be finite fields, and let `C ⊆ Σⁿ` be an `F`-additive code, where `Σ` is a
finite-dimensional `F`-vector space. Suppose `C` is a `τ`-subspace-design code over `K`. For an
integer `a ≥ 1` and `0 < ε < 1`, set `D_a = ⌈2^{5a}/ε⌉`. If `τ(D_a) + ε ≤ 1`, then `C` is
`(1 − τ(D_a) − ε, a, aε²/4)`-`F`-line-decodable.

**Formalization Note.** `K ⊆ F` is an algebra `K → F` of finite fields; `Σ` is an `F`-module, finite
dimensional over `F`, and a `K`-module through `F` (`IsScalarTower K F Σ`). `C` is an
`F`-submodule of `Σⁿ`; "subspace design over `K`" is `IsSubspaceDesign K (C.restrictScalars K)`.
Definition 2.1 requires `τ : ℤ≥1 → [0, 1]` nondecreasing; the published `IsSubspaceDesign` does not
bundle this, so it is stated here as hypotheses on `τ : ℕ → ℝ` restricted to `d ≥ 1`.
`F`-line decodability is `IsCurveDecodable F C 1` (p.42). `D_a` is `⌈2^{5a}/ε⌉₊`. -/
theorem theorem_8_1 (K F : Type) [Field K] [Fintype K] [Field F] [Fintype F] [Algebra K F]
    {Sig : Type} [AddCommGroup Sig] [Module F Sig] [FiniteDimensional F Sig] [Module K Sig]
    [IsScalarTower K F Sig] {n : ℕ} (C : Submodule F (Fin n → Sig)) (τ : ℕ → ℝ)
    (hτ_mono : ∀ d e : ℕ, 1 ≤ d → d ≤ e → τ d ≤ τ e)
    (hτ_range : ∀ d : ℕ, 1 ≤ d → 0 ≤ τ d ∧ τ d ≤ 1)
    (hC : IsSubspaceDesign K (C.restrictScalars K) τ)
    (a : ℕ) (ha : 1 ≤ a) (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hD : τ ⌈(2 : ℝ) ^ (5 * a) / ε⌉₊ + ε ≤ 1) :
    IsCurveDecodable F C 1 (1 - τ ⌈(2 : ℝ) ^ (5 * a) / ε⌉₊ - ε) a (a * ε ^ 2 / 4) := by sorry

end Supplement

end RSSubspaceDesign
