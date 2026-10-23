-- Prove2me | Theorems.Thm_WalledBrauer_SuperSchurWeyl_lemma_7_7
-- name    : WalledBrauer.SuperSchurWeyl.lemma_7_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:16:14.068814+00:00
-- url     : https://prove2.me/theorems/226c9379-2e12-40d7-89a1-a4e099e389a6
-- title:
--   Lemma 7.7 — flip_{r,s} ∘ Φ^{m,n}_{r+s} = Ψ^{m,n}_{r,s} ∘ flip_{r,s}
-- statement:
--   Let $m, n, r, s \ge 0$. The square (7.17)
--
--   $$
--   \begin{array}{ccc}
--   \mathbb C\Sigma_{r+s} & \xrightarrow{\ \mathrm{flip}_{r,s}\ } & B_{r,s}(\delta) \\
--   \big\downarrow{\scriptstyle \Phi^{m,n}_{r+s}} & & \big\downarrow{\scriptstyle \Psi^{m,n}_{r,s}} \\
--   \operatorname{End}(V^{\otimes(r+s)}) & \xrightarrow{\ \mathrm{flip}_{r,s}\ } & \operatorname{End}(V^{\otimes r} \otimes W^{\otimes s})
--   \end{array}
--   $$
--
--   commutes, where the top map is the bijection (2.1) on diagrams and the bottom map is the map (7.16) on endomorphisms. Since all four maps are linear and the permutations are a basis of $\mathbb C\Sigma_{r+s}$, this says: for every $\sigma \in \Sigma_{r+s}$,
--
--   $$
--   \mathrm{flip}_{r,s}\bigl(\Phi^{m,n}_{r+s}(\sigma)\bigr) = \Psi^{m,n}_{r,s}\bigl(\mathrm{flip}_{r,s}(\sigma)\bigr).
--   $$
--
--   Together with Lemma 7.6 and Theorem 7.5 this transports super Schur–Weyl duality from $V^{\otimes(r+s)}$ to $V^{\otimes r} \otimes W^{\otimes s}$.
--
--   **Formalization Note** Stated on the basis: `flipEnd m n r s (PhiDiag m n σ) = PsiDiag m n (flipDiag r s σ)`.
-- source:
--   Brundan and Stroppel, Gradings on walled Brauer algebras and Khovanov's arc algebra, arXiv:1107.0999v1, p. 54, Lemma 7.7 and (7.17)

import Mathlib
import Definitions.Def_WalledBrauer_SuperSchurWeyl_Weights

namespace WalledBrauer.SuperSchurWeyl

/-- Lemma 7.7 (p. 54): the square (7.17) commutes on the basis of `ℂΣ_{r+s}`:
`flip_{r,s}(Φ^{m,n}_{r+s}(σ)) = Ψ^{m,n}_{r,s}(flip_{r,s}(σ))`. -/
theorem lemma_7_7 (m n r s : ℕ) (σ : Equiv.Perm (Fin (r + s))) :
    flipEnd m n r s (PhiDiag m n σ) = PsiDiag m n (flipDiag r s σ) := by sorry

end WalledBrauer.SuperSchurWeyl
