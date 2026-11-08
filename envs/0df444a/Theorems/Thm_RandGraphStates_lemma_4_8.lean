-- Prove2me | Theorems.Thm_RandGraphStates_lemma_4_8
-- name    : RandGraphStates.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:02:13.885654+00:00
-- url     : https://prove2.me/theorems/d75be5e5-6023-4fe7-8d40-006728aa9299
-- title:
--   Lemma 4.8: initial-block reduction
-- statement:
--   Let $H=\bigl[\begin{smallmatrix}M_k&Y\\Y^{T}&Z_s\end{smallmatrix}\bigr]$ be symmetric over $\mathbb F_2$, and set $d:=\mathrm{Nullity}(M_k)$ and $u:=\dim(\ker(M_k)\cap\ker(Y^{T}))$. Then there is a set $T$ of $s-d+u$ of the last $s$ coordinates, chosen from $M_k$ and $Y$ only, such that, with $R$ the block of $Z_s$ on $T$, there is a symmetric matrix $\Gamma$ determined by the entries of $H$ outside $R$ with
--   $$
--   \mathrm{Nullity}(H)=u+\mathrm{Nullity}(R+\Gamma).
--   $$
--   If $H$ has zero diagonal, then $R+\Gamma$ also has zero diagonal.
--
--   This separates a revealed principal submatrix from the remaining random entries, which are still unexposed in $R$.
--
--   **Formalization Note** "$\Gamma$ determined by the entries outside $R$" is written as: for each symmetric $Z$ there is $\Gamma$ serving every symmetric $Z'$ that agrees with $Z$ off $T\times T$.
--
--   Differences from the source:
--   - generalization: after permuting the last s coordinates (T may depend on H); Γ determined by the entries outside R → T chosen before Z, from M_k and Y only; Γ works for every symmetric Z′ agreeing with Z off T × T; reason: the paper's proof gives this ("it does not expose Z_s", p.23) and Lemmas 4.9, 4.10, 4.19 use it; taking Z′ = Z gives the printed statement
--   - encoding: the lower-right block of order s − d + u after a permutation → the block on a Finset T with T.card + d = s + u; reason: a permutation of the last s coordinates only selects T; the addition avoids truncated subtraction
-- source:
--   Chen, Ferber, Goodenough, Sales, Entanglement in random graph states, manuscript (November 2026), Lemma 4.8, p.23

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

/-- **Lemma 4.8** (initial-block reduction). Let `H = [M_k Y; Yᵀ Z_s]` be symmetric over `F₂`, and set
`d := Nullity(M_k)`, `u := dim(ker(M_k) ∩ ker(Yᵀ))`. There is a set `T` of `s - d + u` of the last `s`
coordinates, and a symmetric `Γ`, determined by the entries of `H` outside `R := Z_s[T]`, with
`Nullity(H) = u + Nullity(R + Γ)`. If `H` has zero diagonal, so does `R + Γ`.

Source: Chen, Ferber, Goodenough, Sales, *Entanglement in random graph states*, manuscript (November 2026), Lemma 4.8, p.23.

**Formalization Note.** "After suitably permuting the last `s` coordinates, the lower-right block" is the
choice of `T`. "Determined by the entries outside `R`" is the quantifier order: `T` comes before `Z`
because the paper's proof picks it from `M_k` and `Y` only ("it does not expose `Z_s`", p.23), and `Γ`
serves every symmetric `Z'` that agrees with `Z` off `T × T`. Lemmas 4.9, 4.10 and 4.19 use this form. -/
theorem lemma_4_8 {k s : ℕ} (Mk : Matrix (Fin k) (Fin k) (ZMod 2)) (hMk : Mk.IsSymm)
    (Y : Matrix (Fin k) (Fin s) (ZMod 2)) :
    ∃ T : Finset (Fin s),
      T.card + nullity Mk =
        s + Module.finrank (ZMod 2)
          ↥(LinearMap.ker Mk.mulVecLin ⊓ LinearMap.ker Y.transpose.mulVecLin) ∧
      ∀ Z : Matrix (Fin s) (Fin s) (ZMod 2), Z.IsSymm →
        ∃ Γ : Matrix T T (ZMod 2), Γ.IsSymm ∧
          ∀ Z' : Matrix (Fin s) (Fin s) (ZMod 2), Z'.IsSymm →
            (∀ i j, ¬ (i ∈ T ∧ j ∈ T) → Z' i j = Z i j) →
            nullity (Matrix.fromBlocks Mk Y Y.transpose Z') =
                Module.finrank (ZMod 2)
                    ↥(LinearMap.ker Mk.mulVecLin ⊓ LinearMap.ker Y.transpose.mulVecLin) +
                  nullity (Z'.submatrix ((↑) : T → Fin s) ((↑) : T → Fin s) + Γ) ∧
            ((∀ i, Matrix.fromBlocks Mk Y Y.transpose Z' i i = 0) →
              ∀ i, (Z'.submatrix ((↑) : T → Fin s) ((↑) : T → Fin s) + Γ) i i = 0) := by sorry

end RandGraphStates
