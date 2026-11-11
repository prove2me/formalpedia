-- Prove2me | Theorems.Thm_QuantumSymmetryBreaking_CycleColoring_lemma_4_10
-- name    : QuantumSymmetryBreaking.CycleColoring.lemma_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:26:17.635201+00:00
-- url     : https://prove2.me/theorems/cc1ed149-94f3-481e-a0b2-3c94a0973122
-- title:
--   Lemma 4.10 — $(P_{\pm i}V_nP_{\mp i})'=K_{\pm i}V_n'K_{\pm i}$ with $K_{\pm i}=K_{\pm i}^*$
-- statement:
--   For every $n\ge0$ and every $i\in[s]$, with $Z\mapsto Z'$ the vectorization of Definition 4.9,
--   $$
--   (P_{+i}V_nP_{-i})'=K_{+i}V_n'K_{+i},\qquad (P_{-i}V_nP_{+i})'=K_{-i}V_n'K_{-i},
--   $$
--   where
--   $$
--   K_{\pm i}=K_{\pm i}^*=\tfrac14([e,e]\pm[i,e])([e,e]\mp[e,i])
--   $$
--   are self-adjoint elements of $\mathbb C[G\times G]$. The statement includes both sign choices and the self-adjointness of both $K_{+i}$ and $K_{-i}$.
--
--   The lemma translates the operator recursion of §4.1 into the group algebra, where left and right multiplication by $R_i$ become right multiplication by $[i,e]$; it shows that the vectorized colour operators keep a product form.
--
--   Differences from the source:
--   - encoding: $Z'$ defined for $Z\in\mathcal S$ → `vec Z` is the source's $Z'$ when $Z$ has finitely many nonzero coefficients, and $0$ otherwise; reason: every argument of `vec` in the statement lies in $\mathcal S$ ($V_n\in\mathcal S$ by Lemma 4.3 (V1), and $P_{\pm i}V_nP_{\mp i}$ has finitely many coefficients), so the placeholder is never used
--   - encoding: operators $X$ on $\ell^2(G)$, and $X\in\mathcal S=\operatorname{span}\{|g\rangle\langle h|\}$ → coefficient arrays $X(g,h)=\langle g|X|h\rangle$; $X\in\mathcal S$ means finitely many nonzero coefficients; $L_i,R_i$ act by reindexing; reason: $L_i,R_i$ permute the basis, so every operator in the statement is determined by its coefficients and all products used are reindexings
--   - encoding: generators indexed by $[s]=\{1,\dots,s\}$ → generators indexed by `Fin s` = $\{0,\dots,s-1\}$; reason: relabelling only
--   - encoding: $G=\langle g_1,\dots,g_s\mid g_i^2=e\rangle$ with word length $|g|$ → the universal Coxeter group on `Fin s` (Coxeter matrix with off-diagonal entries 0, Mathlib's encoding of $\infty$) with its Coxeter length; reason: the same presentation; Coxeter length is the reduced-word length
-- source:
--   Flin, Li, Suomela, Quantum Advantage for Distributed Symmetry Breaking, STOC 2027 submission #863 (October 2026), source.pdf SHA-256 121c1ecfd6ed3365b5424f6f5978549d12510d800fb87cb8d2f5e110600a542e, Lemma 4.10, p.18 (PDF p.21)

import Mathlib
import Definitions.Def_QuantumSymmetryBreaking_CycleColoring_GroupAlgebra

namespace QuantumSymmetryBreaking.CycleColoring

/-- Lemma 4.10, Flin, Li, Suomela, *Quantum Advantage for Distributed Symmetry Breaking*, STOC 2027 submission #863 (October 2026), p.18 (PDF p.21).
For all `i ∈ [s]`: `(P_{+i} V_n P_{-i})′ = K_{+i} V_n′ K_{+i}` and
`(P_{-i} V_n P_{+i})′ = K_{-i} V_n′ K_{-i}`, where `K_{±i} = K_{±i}^* = ([e,e] ± [i,e])([e,e] ∓ [e,i])/4`. -/
theorem lemma_4_10 (s n : ℕ) (i : Fin s) :
    vec (projPlusLeft i (projMinusRight i (opV s n))) = Kplus i * vec (opV s n) * Kplus i ∧
    vec (projMinusLeft i (projPlusRight i (opV s n))) = Kminus i * vec (opV s n) * Kminus i ∧
    IsSelfAdj (Kplus i) ∧ IsSelfAdj (Kminus i) := by sorry

end QuantumSymmetryBreaking.CycleColoring
