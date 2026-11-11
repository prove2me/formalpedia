-- Prove2me | Theorems.Thm_RandomColorMix269_Mixing_lemma_5_10
-- name    : RandomColorMix269.Mixing.lemma_5_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:02:32.567497+00:00
-- url     : https://prove2.me/theorems/480294d2-780c-4643-a364-6d7d6a4a54d8
-- title:
--   Lemma 5.10 — buffered percolation: $O(\ln n)$ components of $G[N_G[V^{HD}\cup Z]]$ and tree/unicyclic $G[S]$
-- statement:
--   Fix $\eta\in(0,1)$; there is $d_0>1$ such that for every $d\ge d_0$ the following holds. There are a mark probability $p\in(0,1)$ depending on $\eta,d$ and, for every $J>0$, a constant $0<K_J<\infty$ such that, when each vertex of $G\sim G(n,d/n)$ is marked independently with probability $p$ (forming $Z$) and $A=V^{HD}\cup Z$,
--   $$
--   \mathbb P_{G,Z}\Big(\max_{R\text{ component of }G[N_G[A]]}|R|>K_J\ln n\Big)\le n^{-J}
--   $$
--   for all sufficiently large $n$. Moreover there is $A_0>0$ such that, with probability at least $1-A_0/n$ over $G$ for all large $n$, every component of $G[S]$, $S=N_G[V^{HD}]$, is a tree or unicyclic and has at most $K_1\ln n$ vertices.
--
--   The first clause controls random blocks (Lemma 5.14); the second is the geometric event used by Propositions 5.11 and 5.17.
--
--   Differences from the source:
--   - encoding: vertex set [n] and colour set [q] → Fin n and Fin q; reason: relabelling only
--   - encoding: probability at least 1 − O_{η,d}(n^{-1}) → ∃ A>0, for all large n, probability ≥ 1 − A/n; reason: definition of the O-term
--   - encoding: K_J < ∞ → K_J > 0 real; reason: enlarging K_J only shrinks the failure event, so a positive constant exists iff a finite one does
--   - encoding: tree or unicyclic component → component with at most as many edges as vertices; reason: a connected graph has |E| ≤ |V| exactly when it is a tree or unicyclic
--   - encoding: independent graph edges of probability d/n → the published edge law clamps d/n to [0,1]; reason: all probability estimates are eventual in n, so the finitely many n < d have no effect
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #269 (October 2026), PDF sha256 467638f1abc0f57df1bc0dcd9abfd308eb90ddbaf4947dac3eefa5f293ac6f05, p.30, Lemma 5.10

import Definitions.Def_RandomColorMix269_Mixing_Geometry

open scoped Classical BigOperators
set_option autoImplicit false

namespace RandomColorMix269.Mixing

/-- Lemma 5.10, p.30: joint graph/mark tails and the separate graph geometry event. -/
theorem lemma_5_10 :
    ∀ η : ℝ, 0 < η → η < 1 → ∃ d₀ : ℝ, 1 < d₀ ∧
      ∀ d : ℝ, d₀ ≤ d → ∃ (p : ℝ) (K : ℝ → ℝ), PercolationConstants η d p K := by sorry

end RandomColorMix269.Mixing
