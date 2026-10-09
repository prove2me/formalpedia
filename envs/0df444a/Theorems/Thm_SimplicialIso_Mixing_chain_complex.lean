-- Prove2me | Theorems.Thm_SimplicialIso_Mixing_chain_complex
-- name    : SimplicialIso.Mixing.chain_complex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:22:13.250001+00:00
-- url     : https://prove2.me/theorems/31994485-3025-4853-99fc-5ad0079c0888
-- title:
--   p. 6 — chain complex: ∂_{d−1}∂_d = 0, and dually ∂*_d∂*_{d−1} = 0, on a complex with a complete skeleton
-- statement:
--   Let $X$ be a $d$-dimensional complex with a complete skeleton on $n$ vertices, $d\ge1$. The boundary operators compose to zero,
--   $$\partial_{d-1}\partial_d=0\quad\text{on }\Omega^d,$$
--   and dually the co-boundary operators compose to zero, $\partial_d^*\partial_{d-1}^*=0$ on $\Omega^{d-2}$; that is, every exact $(d-1)$-form is closed, $B^{d-1}\subseteq Z^{d-1}=\ker\partial_d^*$.
--
--   This is the chain-complex property of $(\Omega^j,\partial_j)$ at $j=d$. Its dual form gives $B^{d-1}\subseteq\ker\Delta^+$, which the proof of the Mixing Lemma uses in (4.8).
--
--   **Formalization Note.** $d\ge1$ is added because the Laplacians act on $\Omega^{d-1}$. The first identity is stated for every function on $(d+1)$-sets ($\partial_d$ ignores values off $X^d$). The dual identity is the adjoint statement of $\partial_{d-1}\partial_d=0$, stated by the formulas.
-- source:
--   Parzanchevski, Rosenthal and Tessler, Isoperimetric inequalities in simplicial complexes, arXiv:1207.0638v3, p. 6, 'The sequence (Ω^j, ∂_j) is a chain complex, i.e., ∂_{j−1}∂_j = 0 for all j', case j = d, and its dual

import Mathlib
import Definitions.Def_SimplicialIso_Mixing_Setting

namespace SimplicialIso.Mixing

open Finset
open scoped InnerProductSpace

/-- p. 6: `(Ω^j, ∂_j)` is a chain complex, here at `j = d`: `∂_{d-1} ∂_d = 0`; dually
`∂*_d ∂*_{d-1} = 0`, i.e. every exact `(d-1)`-form is closed. -/
theorem chain_complex (n d : ℕ) (hd : 1 ≤ d) (X : Complex n d) :
    (∀ g : Form n (d + 1), bdLow n d (bdTop X g) = 0) ∧
      (∀ h : Form n (d - 1), cobdTop X (cobdLow n d h) = 0) := by sorry

end SimplicialIso.Mixing
