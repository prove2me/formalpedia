-- Prove2me | Theorems.Thm_TalagrandConc_SymmetricGroup_lemma_5_10
-- name    : TalagrandConc.SymmetricGroup.lemma_5_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:43:22.098863+00:00
-- url     : https://prove2.me/theorems/83114783-83ec-4403-ad63-5a00c4d9e66c
-- title:
--   Lemma 5.10 — assuming (5.3)_N or (5.4)_N, ∫ exp(g(A,σ,N+1,σ⁻¹(j))/16) dQ'_i ≤ 1/Q'_j(A)
-- statement:
--   Assume that one of the induction hypotheses $(5.3)_N$, $(5.4)_N$ holds for every subset of $S_N$ and every $p\le N$. Let $A\subseteq S_{N+1}$ and $i,j\le N+1$ with $i\ne j$. Let $Q'_i$ and $Q'_j$ be the uniform probabilities on $G'_i$ and $G'_j$, where $G'_k=\{\sigma\in S_{N+1}:\sigma(N+1)=k\}$. Then
--   $$\int\exp\frac1{16}g\bigl(A,\sigma,N+1,\sigma^{-1}(j)\bigr)\,dQ'_i(\sigma)\le\frac1{Q'_j(A)}.\tag{5.17}$$
--
--   This is the counterpart of Lemma 5.6 in the proof of $(5.3)_{N+1}$.
--
--   **Formalization Note** The paper says (5.17) follows "from either $(5.3)_N$ or $(5.4)_N$", so the hypothesis is `Ineq53 N ∨ Ineq54 N`.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 150, Lemma 5.10, Eq. (5.17) (proof Eq. (5.18))

import Mathlib
import Definitions.Def_TalagrandConc_SymmetricGroup_Basic

namespace TalagrandConc.SymmetricGroup

open scoped ENNReal
open Equiv

theorem lemma_5_10 {N : ℕ} (hIH : Ineq53 N ∨ Ineq54 N) (A : Set (Perm (Fin (N + 1))))
    (i j : Fin (N + 1)) (hij : i ≠ j) :
    uniformAvg (G' N i) (fun σ => exp16 (g A σ (Fin.last N) (σ⁻¹ j)))
      ≤ (uniformProb (G' N j) A)⁻¹ := by sorry
end TalagrandConc.SymmetricGroup
