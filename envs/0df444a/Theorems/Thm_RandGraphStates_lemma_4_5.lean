-- Prove2me | Theorems.Thm_RandGraphStates_lemma_4_5
-- name    : RandGraphStates.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:02:07.39414+00:00
-- url     : https://prove2.me/theorems/e5749220-51e2-4d35-94d7-a48613f0ac47
-- title:
--   Lemma 4.5: Fourier step
-- statement:
--   Let $M$ be a fixed symmetric $k\times k$ matrix over $\mathbb F_2$ with $d:=\mathrm{Nullity}(M)$, let $a\in\mathbb F_2^k$, let $x\in\mathbb F_2^k$ have independent $\mathrm{Ber}(p)$ coordinates, $0<p<1$, and put $q=1-2p$. Then
--   $$
--   \Pr\bigl(x\in a+\mathrm{im}(M)\bigr)=2^{-d}\sum_{\lambda\in\ker(M)}(-1)^{\langle\lambda,a\rangle}q^{|\lambda|}\le 2^{-d}+2^{-d}\sum_{0\ne\lambda\in\ker(M)}|q|^{|\lambda|}.
--   $$
--   The identity expresses the step probability of the nullity path through the weights of kernel vectors, and allows the comparison with the uniform value $2^{-d}$.
--
--   Differences from the source:
--   - encoding: (−1)^{⟨λ,a⟩} → (−1) to the power of the representative in {0, 1} of the dot product in F₂; reason: the same sign
-- source:
--   Chen, Ferber, Goodenough, Sales, Entanglement in random graph states, manuscript (November 2026), Lemma 4.5, p.21

import Mathlib
import Definitions.Def_BollobasChromatic_Main_Setting
import Definitions.Def_RandGraphStates_alphaLC
import Definitions.Def_SquashedKey_KeyBoundFunction
import Definitions.Def_RandGraphStates_cEtaEps
import Definitions.Def_RandGraphStates_pMinus
import Definitions.Def_RandGraphStates_Cunif
import Definitions.Def_RandGraphStates_nullity
import Definitions.Def_RandGraphStates_piTail

set_option autoImplicit false

open BollobasChromatic.Main
open Filter Topology

namespace RandGraphStates

/-- **Lemma 4.5** (Fourier step). Let `M` be a fixed symmetric `k × k` matrix, `d := Nullity(M)`,
`a ∈ F₂^k`, and let `x` have independent `Ber(p)` coordinates. With `q = 1 - 2p`,
`Pr(x ∈ a + im(M)) = 2^{-d} Σ_{λ ∈ ker(M)} (-1)^{⟨λ,a⟩} q^{|λ|} ≤ 2^{-d} + 2^{-d} Σ_{0 ≠ λ ∈ ker(M)} |q|^{|λ|}`.

Source: Chen, Ferber, Goodenough, Sales, *Entanglement in random graph states*, manuscript (November 2026), Lemma 4.5, p.21.

**Formalization Note.** `(-1)^{⟨λ,a⟩}` is computed from the representative of `⟨λ,a⟩ ∈ F₂` in `{0, 1}`.
`0 < p < 1` is the standing assumption of §4, p.17. -/
theorem lemma_4_5 {k : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (M : Matrix (Fin k) (Fin k) (ZMod 2)) (hM : M.IsSymm) (a : Fin k → ZMod 2) :
    (∑ x : Fin k → ZMod 2, if ∃ y : Fin k → ZMod 2, x = a + M.mulVec y then berWeight p x else 0) =
        (2 : ℝ) ^ (-(nullity M : ℤ)) *
          ∑ l ∈ Finset.univ.filter (fun l : Fin k → ZMod 2 => M.mulVec l = 0),
            (-1 : ℝ) ^ (dotProduct l a).val * (qOf p) ^ hammingNorm l ∧
    (∑ x : Fin k → ZMod 2, if ∃ y : Fin k → ZMod 2, x = a + M.mulVec y then berWeight p x else 0) ≤
        (2 : ℝ) ^ (-(nullity M : ℤ)) +
          (2 : ℝ) ^ (-(nullity M : ℤ)) *
            ∑ l ∈ Finset.univ.filter (fun l : Fin k → ZMod 2 => l ≠ 0 ∧ M.mulVec l = 0),
              |qOf p| ^ hammingNorm l := by sorry

end RandGraphStates
