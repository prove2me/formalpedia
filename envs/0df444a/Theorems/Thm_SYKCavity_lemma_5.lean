-- Prove2me | Theorems.Thm_SYKCavity_lemma_5
-- name    : SYKCavity.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:35:22.769734+00:00
-- url     : https://prove2.me/theorems/34762c1c-65ea-4655-ad32-a71d0264b4ac
-- title:
--   Lemma 5 — for every $\beta\ge0$ the ladder operator $\mathfrak L_\beta$ is invertible and $\|\mathfrak L_\beta^{-1}X\|_\infty\le C_\beta\|X\|_\infty$
-- statement:
--   For every constant $\beta\ge0$ the ladder operator
--   $$(\mathfrak L_\beta X)(u,v)=X(u,v)-3\beta^2\int_0^1\!\!\int_0^1G_*(u,s)G_*(s,t)^2X(s,t)G_*(t,v)\,ds\,dt$$
--   is invertible on antisymmetric kernels in $L^2([0,1]^2)$, and there is $C_\beta$ with
--   $$\|\mathfrak L_\beta^{-1}X\|_\infty\le C_\beta\|X\|_\infty.\qquad(4.11)$$
--
--   This is the step that removes any temperature restriction: the hierarchy (4.9) is solved by applying $\mathfrak L_\beta^{-1}$ to its first pair of variables at every $\beta\ge0$.
--
--   **Formalization Note** Invertibility is `IsRegular β` (a bijection of the antisymmetric $L^2$ classes); the bound is for every antisymmetric $X\in L^2$ and its preimage.
--
--   Differences from the source:
--   - encoding: L_β invertible (on antisymmetric kernels in L²([0,1]²)) → `IsRegular β`: every antisymmetric X ∈ L² is L_β Y for a unique antisymmetric Y ∈ L² (up to a.e. equality); reason: Appendix H, p.129; L_β is bounded, so the inverse is bounded by the open mapping theorem
--   - reading: ‖·‖∞ "including the prescribed coincident-time values" (p.131) → the essential supremum on [0,1]²; reason: the statement concerns the L² inverse, whose elements carry no point values
-- source:
--   Schmidhuber–Zlokapa, Polynomial-time algorithms for mean-field models up to the glass transition, arXiv:2610.06807 (held version, sha256 25d817ba…cfc5), Lemma 5, p.27, (4.11); Appendix H, pp.129–131

import Mathlib
import Definitions.Def_SYKCavity_Ladder

open MeasureTheory

namespace SYKCavity

/-- **Lemma 5 (Ladder kernel inversion)**, p.27 of A. Schmidhuber, A. Zlokapa, *Polynomial-time
algorithms for mean-field models up to the glass transition*, arXiv:2610.06807 (held version, sha256
25d817ba…cfc5), (4.11).

For every `β ≥ 0` the operator `L_β` is invertible, and there is `C_β` with
`‖L_β^{−1} X‖∞ ≤ C_β ‖X‖∞`.

**Formalization Note.** Invertibility is `IsRegular β`: `L_β` is a bijection of the antisymmetric
kernels in `L²([0,1]²)` (Appendix H, p.129). The bound is stated for every antisymmetric `X ∈ L²` and
its preimage `Y = L_β^{−1} X`; `‖·‖∞` is the essential supremum. -/
theorem lemma_5 (β : ℝ) (hβ : 0 ≤ β) :
    IsRegular β ∧
      ∃ C : ℝ, ∀ X Y : ℝ × ℝ → ℝ, MemLp X 2 sq → Antisym X → MemLp Y 2 sq → Antisym Y →
        ladder β Y =ᵐ[sq] X → eLpNorm Y ⊤ sq ≤ ENNReal.ofReal C * eLpNorm X ⊤ sq := by sorry

end SYKCavity
