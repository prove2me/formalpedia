-- Prove2me | Theorems.Thm_TalagrandConc_SymmetricGroup_prop_5_2
-- name    : TalagrandConc.SymmetricGroup.prop_5_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:45:07.946158+00:00
-- url     : https://prove2.me/theorems/a7f93a5f-5b8d-41eb-97cc-444f08adb78c
-- title:
--   Proposition 5.2 — (5.3)_N and (5.4)_N: ∫ exp(f(A,σ,p)/16) dP_N ≤ 1/P_N(A), and with p replaced by σ⁻¹(p)
-- statement:
--   For every $N$, every subset $A$ of the symmetric group $S_N$ and every $p\le N$,
--   $$\int_{S_N}\exp\frac1{16}f(A,\sigma,p)\,dP_N(\sigma)\le\frac1{P_N(A)},\qquad(5.3)_N$$
--   $$\int_{S_N}\exp\frac1{16}f\bigl(A,\sigma,\sigma^{-1}(p)\bigr)\,dP_N(\sigma)\le\frac1{P_N(A)}.\qquad(5.4)_N$$
--   Here $P_N$ is the uniform probability on $S_N$, and $f(A,\sigma,p)$ is the convex-distance functional in which coordinate $p$ is counted twice.
--
--   Theorem 5.1 itself cannot be proved by induction on $N$. This strengthened pair of inequalities can, and since $f(A,\sigma)\le f(A,\sigma,p)$ it implies Theorem 5.1. The induction is crossed: $(5.4)_{N+1}$ uses $(5.3)_N$, and $(5.3)_{N+1}$ uses $(5.4)_N$.
--
--   **Formalization Note** If $A=\emptyset$, both sides are $+\infty$. For $N=0$ there is no $p$ and the statement is empty. The paper leaves the base case $N=1$ to the reader.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 145, Proposition 5.2, Eqs. (5.3)_N, (5.4)_N

import Mathlib
import Definitions.Def_TalagrandConc_SymmetricGroup_Basic

namespace TalagrandConc.SymmetricGroup

open scoped ENNReal
open Equiv

theorem prop_5_2 {N : ℕ} (A : Set (Perm (Fin N))) (p : Fin N) :
    uniformAvg Finset.univ (fun σ => exp16 (fp A σ p)) ≤ (PN A)⁻¹ ∧
      uniformAvg Finset.univ (fun σ => exp16 (fp A σ (σ⁻¹ p))) ≤ (PN A)⁻¹ := by sorry
end TalagrandConc.SymmetricGroup
