-- Prove2me | Theorems.Thm_WalledBrauer_SuperSchurWeyl_lemma_7_4
-- name    : WalledBrauer.SuperSchurWeyl.lemma_7_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:16:07.049241+00:00
-- url     : https://prove2.me/theorems/e8966d78-63ab-490a-bd94-4b191d80a87b
-- title:
--   Lemma 7.4 — the right B_{r,s}(δ)-action (7.7) on V^{⊗r} ⊗ W^{⊗s}, "(a b)" acting as Ω_{a,b}
-- statement:
--   Let $m, n, r, s \ge 0$, $\delta = m - n$, and let walled Brauer diagrams $\sigma$ act on $V^{\otimes r} \otimes W^{\otimes s}$ by (7.7),
--
--   $$
--   v_{\mathbf i^{\mathrm L}} \otimes w_{\mathbf i^{\mathrm R}} \cdot \sigma = \sum_{\mathbf j \in I^{r+s}} \mathrm{wt}({}_{\mathbf i}\sigma_{\mathbf j})\, v_{\mathbf j^{\mathrm L}} \otimes w_{\mathbf j^{\mathrm R}} .
--   $$
--
--   Write $\Psi(\sigma)$ for this operator. Then:
--
--   1. this is a right $B_{r,s}(\delta)$-module structure: the identity diagram acts as $1$, and whenever $\sigma\tau = \delta^t \pi$ in $B_{r,s}(\delta)$ — $\pi$ is obtained by putting $\sigma$ under $\tau$ and removing the $t$ internal circles —
--   $$
--   \Psi(\tau)\,\Psi(\sigma) = \delta^t\, \Psi(\pi);
--   $$
--   2. for $1 \le a < b \le r+s$ the "transposition" $\overline{(a\ b)} \in B_{r,s}(\delta)$, which is $\mathrm{flip}_{r,s}((a\ b))$ if $a$ and $b$ are on the same side of the wall and $-\mathrm{flip}_{r,s}((a\ b))$ otherwise (p. 7), acts as the operator $\Omega_{a,b}$ of (7.3);
--   3. hence every $\Psi(\sigma)$ lies in $\operatorname{End}_{\mathfrak g}(V^{\otimes r} \otimes W^{\otimes s})$.
--
--   The lemma constructs the walled Brauer side of mixed Schur–Weyl duality: the homomorphism $\Psi^{m,n}_{r,s}$ of (7.12) into $\operatorname{End}_{\mathfrak g}(V^{\otimes r} \otimes W^{\otimes s})^{\mathrm{op}}$.
--
--   **Formalization Note** Diagrams are the published `WalledBrauer.Blocks.WalledDiagram r s`, whose product `comp A B` stacks `A` over `B`; the paper's "$\sigma$ under $\tau$" is therefore `comp τ σ`, with `loops τ.1 σ.1` circles. The matrix of $\Psi(\sigma)$ has column = input, so the right action reads `PsiDiag τ * PsiDiag σ = δ ^ t • PsiDiag (comp τ σ)`, with `δ = (m : ℂ) - n`. Positions are 0-based.
-- source:
--   Brundan and Stroppel, Gradings on walled Brauer algebras and Khovanov's arc algebra, arXiv:1107.0999v1, p. 51, Lemma 7.4, (7.7), (7.8); the "transpositions" (a b) in B_{r,s}(δ), p. 7

import Mathlib
import Definitions.Def_WalledBrauer_SuperSchurWeyl_Weights

namespace WalledBrauer.SuperSchurWeyl

open WalledBrauer.Blocks

/-- Lemma 7.4 (p. 51): (7.7) defines a right `B_{r,s}(δ)`-module structure on
`V^{⊗ r} ⊗ W^{⊗ s}`, `δ = m - n`: the identity diagram acts as `1`, and if `σ τ = δ^t π`
(`π` is `σ` drawn under `τ`, i.e. `WalledDiagram.comp τ σ`, with `t` circles removed) then
`Ψ(τ) Ψ(σ) = δ^t Ψ(π)`; the "transposition" `(a b)` (`± flip_{r,s}((a b))`, sign `-` iff `a`
and `b` are on opposite sides of the wall) acts as `Ω_{a,b}`; and every diagram acts by an
element of `End_g`. -/
theorem lemma_7_4 (m n r s : ℕ) :
    PsiDiag m n (WalledDiagram.one r s) = 1 ∧
    (∀ σ τ : WalledDiagram r s, PsiDiag m n τ * PsiDiag m n σ =
        delta m n ^ loops τ.1 σ.1 • PsiDiag m n (WalledDiagram.comp τ σ)) ∧
    (∀ a b : Fin (r + s), a < b →
        (if (a.val < r ↔ b.val < r) then (1 : ℂ) else -1) •
            PsiDiag m n (flipDiag r s (Equiv.swap a b)) = Omega m n (mixed r s) a b) ∧
    (∀ σ : WalledDiagram r s, PsiDiag m n σ ∈ EndG m n (mixed r s)) := by sorry

end WalledBrauer.SuperSchurWeyl
