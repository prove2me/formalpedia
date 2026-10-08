-- Prove2me | Theorems.Thm_TalagrandConc_SymmetricGroup_theorem_5_1
-- name    : TalagrandConc.SymmetricGroup.theorem_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:43:55.485336+00:00
-- url     : https://prove2.me/theorems/5d946505-9316-4e5f-b5c1-cf7e2021b0df
-- title:
--   Theorem 5.1 — ∫ exp(f(A,σ)/16) dP_N(σ) ≤ 1/P_N(A) on the symmetric group
-- statement:
--   Let $S_N$ be the group of permutations of $\{1,\dots,N\}$ with its uniform probability $P_N$. For $A\subseteq S_N$ and $\sigma\in S_N$, let $f(A,\sigma)$ be the squared Euclidean distance from $0$ to the convex hull $V_A(\sigma)$ of
--   $$U_A(\sigma)=\bigl\{s\in\{0,1\}^N:\ \exists\tau\in A,\ \forall\ell,\ s_\ell=0\Rightarrow\tau(\ell)=\sigma(\ell)\bigr\}.$$
--   Then for every subset $A$ of $S_N$,
--   $$\int_{S_N}\exp\frac1{16}f(A,\sigma)\,dP_N(\sigma)\le\frac1{P_N(A)}.\tag{5.2}$$
--
--   This is the analogue on $S_N$ of Theorem 4.1.1, the convex hull inequality on product spaces. It improves Maurey's concentration inequality for the symmetric group in the same way that Theorem 4.1.1 improves the Hamming-distance bound (2.1.3). By Markov's inequality it gives $P_N(A)\,P_N\{f(A,\cdot)\ge t\}\le e^{-t/16}$.
--
--   **Formalization Note** $\int\cdot\,dP_N$ is the finite average $\frac1{N!}\sum_{\sigma\in S_N}$. The functional $f$ takes values in $[0,+\infty]$, and $\exp(+\infty)=+\infty$. For $A=\emptyset$, both sides equal $+\infty$.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 145, Theorem 5.1, Eq. (5.2)

import Mathlib
import Definitions.Def_TalagrandConc_SymmetricGroup_Basic

namespace TalagrandConc.SymmetricGroup

open scoped ENNReal
open Equiv

theorem theorem_5_1 {N : ℕ} (A : Set (Perm (Fin N))) :
    uniformAvg Finset.univ (fun σ => exp16 (f A σ)) ≤ (PN A)⁻¹ := by sorry
end TalagrandConc.SymmetricGroup
