-- Prove2me | Theorems.Thm_SYKCavity_lemma_60
-- name    : SYKCavity.lemma_60
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:35:22.897351+00:00
-- url     : https://prove2.me/theorems/3b0cebc8-556c-43dd-9fb4-949d3df37a47
-- title:
--   Lemma 60 — $\|\mathfrak L_\beta^{-1}X\|_\infty\le(1+3\beta^2/16+9\beta^4/256\cdot\|\mathfrak L_\beta^{-1}\|_{2\to2})\|X\|_\infty$ at regular temperatures
-- statement:
--   Let $\beta\ge0$ be a temperature at which the $L^2$ inverse of the ladder operator $\mathfrak L_\beta$ (3.30) exists on antisymmetric kernels in $L^2([0,1]^2)$. Then for every antisymmetric $X\in L^2([0,1]^2)$,
--   $$\|\mathfrak L_\beta^{-1}X\|_\infty\le\Bigl(1+\frac{3\beta^2}{16}+\frac{9\beta^4}{256}\,\|\mathfrak L_\beta^{-1}\|_{2\to2}\Bigr)\|X\|_\infty.\qquad(H.11)$$
--
--   The explicit constant turns an $L^2$ inverse into a uniform bound, which is what the recursion for the centered moments needs; Lemma 5 then follows once invertibility is known at every temperature.
--
--   **Formalization Note** $Y=\mathfrak L_\beta^{-1}X$ is the antisymmetric $L^2$ kernel with $\mathfrak L_\beta Y=X$ almost everywhere. The operator norm enters through any $c\ge0$ with $\|Y\|_2\le c\|\mathfrak L_\beta Y\|_2$ for all antisymmetric $Y\in L^2$.
--
--   Differences from the source:
--   - encoding: L_β on antisymmetric kernels in L²([0,1]²) and its L² inverse → functions ℝ² → ℝ with MemLp 2 on [0,1]² and a.e. antisymmetry, equalities a.e.; `IsRegular β` = L_β is a bijection of these classes; Y with L_β Y = X a.e.; reason: Appendix H, p.129: "We work on antisymmetric kernels in L2([0, 1]2)"
--   - encoding: ‖L_β^{−1}‖_{2→2} → every c ≥ 0 with ‖Y‖₂ ≤ c‖L_β Y‖₂ for all antisymmetric Y ∈ L²; reason: the operator norm of the inverse is the least such c and the bound is monotone in c, so this is (H.11)
--   - reading: ‖·‖∞, which in the proof (H.16) includes the prescribed coincident-time values → the essential supremum on [0,1]²; reason: (H.11) is an inequality for the L² inverse, whose elements carry no point values; the coincident-time refinement concerns representatives of the hierarchy's kernels
-- source:
--   Schmidhuber–Zlokapa, Polynomial-time algorithms for mean-field models up to the glass transition, arXiv:2610.06807 (held version, sha256 25d817ba…cfc5), Lemma 60, p.132, (H.11); Appendix H, p.129

import Mathlib
import Definitions.Def_SYKCavity_Ladder

open MeasureTheory

namespace SYKCavity

/-- **Lemma 60 (Uniform representatives and coincident-time evaluations)**, p.132 of A. Schmidhuber,
A. Zlokapa, *Polynomial-time algorithms for mean-field models up to the glass transition*,
arXiv:2610.06807 (held version, sha256 25d817ba…cfc5), (H.11).

At any temperature `β ≥ 0` where the `L²` inverse of `L_β` exists,
`‖L_β^{−1} X‖∞ ≤ (1 + 3β²/16 + 9β⁴/256 · ‖L_β^{−1}‖_{2→2}) ‖X‖∞`.

**Formalization Note.** `L_β` acts on antisymmetric kernels in `L²([0,1]²)` (`ladder`, `Antisym`,
`MemLp · 2 sq`); `IsRegular β` says the inverse exists. `‖L_β^{−1}‖_{2→2}` enters through any `c ≥ 0`
with `‖Y‖₂ ≤ c ‖L_β Y‖₂` for all antisymmetric `Y ∈ L²`: the operator norm of the inverse is the least
such `c`, and the bound is monotone in `c`, so the statement for all such `c` is (H.11). `Y` is
`L_β^{−1} X` (`L_β Y = X` a.e.). `‖·‖∞` is the essential supremum on `[0,1]²`. -/
theorem lemma_60 (β : ℝ) (hβ : 0 ≤ β) (hreg : IsRegular β) (c : ℝ) (hc : 0 ≤ c)
    (hinv : ∀ Y : ℝ × ℝ → ℝ, MemLp Y 2 sq → Antisym Y →
      eLpNorm Y 2 sq ≤ ENNReal.ofReal c * eLpNorm (ladder β Y) 2 sq)
    (X Y : ℝ × ℝ → ℝ) (hX : MemLp X 2 sq) (hXa : Antisym X) (hY : MemLp Y 2 sq)
    (hYa : Antisym Y) (hLY : ladder β Y =ᵐ[sq] X) :
    eLpNorm Y ⊤ sq ≤
      ENNReal.ofReal (1 + 3 * β ^ 2 / 16 + 9 * β ^ 4 / 256 * c) * eLpNorm X ⊤ sq := by sorry

end SYKCavity
