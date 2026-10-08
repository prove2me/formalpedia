-- Prove2me | Theorems.Thm_TalagrandConc_SymmetricGroup_lemma_5_6
-- name    : TalagrandConc.SymmetricGroup.lemma_5_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:42:56.049248+00:00
-- url     : https://prove2.me/theorems/9a3f70ef-15e2-49f6-a343-bf1c1552c66f
-- title:
--   Lemma 5.6 — assuming (5.3)_N or (5.4)_N, ∫ exp(g(A,σ,i,j)/16) dQ_i ≤ 1/Q_j(A)
-- statement:
--   Assume that one of the induction hypotheses $(5.3)_N$, $(5.4)_N$ holds for every subset of $S_N$ and every $p\le N$. Let $A\subseteq S_{N+1}$ and $i,j\le N+1$ with $j\ne i$. Let $Q_i$ and $Q_j$ be the uniform probabilities on $G_i$ and $G_j$, where $G_k=\{\sigma\in S_{N+1}:\sigma(k)=N+1\}$. Then
--   $$\int\exp\frac1{16}g(A,\sigma,i,j)\,dQ_i(\sigma)\le\frac1{Q_j(A)}.\tag{5.11}$$
--
--   The integral is over $G_i$, but the bound involves the mass of $A$ on a different block $G_j$. This bound is the second factor in the Hölder step of the proof of $(5.4)_{N+1}$, and it is why that proof chooses $j$ to maximize $Q_j(A)$.
--
--   **Formalization Note** The statement is part of the induction step of Proposition 5.2. The paper says it "will follow from either $(5.3)_N$ or $(5.4)_N$", so the hypothesis is the disjunction `Ineq53 N ∨ Ineq54 N`. $Q_j(A)=|A\cap G_j|/|G_j|$.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 147, Lemma 5.6, Eq. (5.11) (proof p. 148, Eq. (5.12))

import Mathlib
import Definitions.Def_TalagrandConc_SymmetricGroup_Basic

namespace TalagrandConc.SymmetricGroup

open scoped ENNReal
open Equiv

theorem lemma_5_6 {N : ℕ} (hIH : Ineq53 N ∨ Ineq54 N) (A : Set (Perm (Fin (N + 1))))
    (i j : Fin (N + 1)) (hji : j ≠ i) :
    uniformAvg (G N i) (fun σ => exp16 (g A σ i j)) ≤ (uniformProb (G N j) A)⁻¹ := by sorry
end TalagrandConc.SymmetricGroup
