-- Prove2me | Theorems.Thm_RandGraphStates_lemma_4_9
-- name    : RandGraphStates.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:02:22.077202+00:00
-- url     : https://prove2.me/theorems/0d341095-f334-4479-82c5-0ccf3b0829cd
-- title:
--   Lemma 4.9: uniform initial segment
-- statement:
--   Let $M_k$ be a fixed symmetric $k\times k$ matrix with $d:=\mathrm{Nullity}(M_k)$, and let $\widetilde M=\bigl[\begin{smallmatrix}M_k&Y\\Y^{T}&Z_s\end{smallmatrix}\bigr]$, where the entries of $Y$ and the off-diagonal entries of $Z_s$ are independent $\mathrm{Ber}(1/2)$ variables and the diagonal of $Z_s$ is prescribed. For a nonnegative integer $t$, if $s-d-t\to\infty$, then
--   $$
--   \Pr\bigl(\mathrm{Nullity}(\widetilde M)\ge t\mid M_k\bigr)\le\bigl(C_{\mathrm{unif}}+o(1)\bigr)2^{-\binom t2}.
--   $$
--   So conditioning on $M_k$ preserves the tail of Corollary 4.4 when the random block is large relative to $d$ and $t$. $M_k$ need not have zero diagonal.
--
--   Differences from the source:
--   - encoding: s − d − t → ∞ with o(1) → ∀ δ > 0, ∃ L, ∀ k s t M_k and diagonal with t + d + L ≤ s: the bound with C_unif + δ; reason: equivalent by a diagonal argument; the uniformity over the parameters is the quantifier order
--   - encoding: Pr(· | M_k) → M_k a fixed parameter; the probability is over Y and the graph; reason: conditioning on a fixed block, as the paper writes it
-- source:
--   Chen, Ferber, Goodenough, Sales, Entanglement in random graph states, manuscript (November 2026), Lemma 4.9, p.24

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

/-- **Lemma 4.9** (uniform initial segment). Let `M_k` be a fixed symmetric `k × k` matrix with
`d := Nullity(M_k)`, and `M̃ = [M_k Y; Yᵀ Z_s]` with `Y` and the off-diagonal entries of `Z_s` independent
`Ber(1/2)` and the diagonal of `Z_s` prescribed. For `t ≥ 0`, if `s - d - t → ∞`, then
`Pr(Nullity(M̃) ≥ t | M_k) ≤ (C_unif + o(1)) 2^{-C(t,2)}`.

Source: Chen, Ferber, Goodenough, Sales, *Entanglement in random graph states*, manuscript (November 2026), Lemma 4.9, p.24.

**Formalization Note.** The `o(1)` as `s - d - t → ∞` is unfolded: for each `δ > 0` there is `L`, uniform over
`k, s, t, M_k` and the diagonal, such that `s - d - t ≥ L` gives the bound with `δ`. -/
theorem lemma_4_9 :
    ∀ δ : ℝ, 0 < δ → ∃ L : ℕ, ∀ (k s t : ℕ) (Mk : Matrix (Fin k) (Fin k) (ZMod 2))
      (b : Fin s → ZMod 2), Mk.IsSymm → t + nullity Mk + L ≤ s →
      blockTail (1 / 2) Mk b t ≤ (Cunif + δ) * (2 : ℝ) ^ (-((t.choose 2 : ℕ) : ℤ)) := by sorry

end RandGraphStates
