-- Prove2me | Theorems.Thm_SchrijverSFM_Ring_ring_family_reduction
-- name    : SchrijverSFM.Ring.ring_family_reduction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:05:53.248636+00:00
-- url     : https://prove2.me/theorems/1a26d1b1-ac51-40d1-bbb0-0169bb3b69bd
-- title:
--   §6, p. 354 — Schrijver's ring-family reduction: g of (26) is submodular (27), and minimizing g − c over 2^V yields a minimizer of f over 𝒞
-- statement:
--   Let $V$ be a finite set and $\mathcal C$ a **ring family** of subsets of $V$, i.e. closed under union and intersection, normalized as in the paper so that $\emptyset \in \mathcal C$, $V \in \mathcal C$, and $M_u \ne M_v$ for all $u \ne v$, where $M_v$ is the smallest set of $\mathcal C$ containing $v$. Let $f : 2^V \to \mathbb R$ be submodular on $\mathcal C$:
--   $$f(X \cup Y) + f(X \cap Y) \le f(X) + f(Y) \qquad (X, Y \in \mathcal C).$$
--   For $v \in V$ let $L_v$ be the largest set of $\mathcal C$ not containing $v$, let
--   $$c(v) := \max\{0,\ f(L_v) - f(L_v \cup \{v\})\}$$
--   as in (23), and $c(X) := \sum_{v \in X} c(v)$. For $X \subseteq V$ let $\overline X$ be the smallest set of $\mathcal C$ containing $X$ and $g(X) := f(\overline X) + c(\overline X)$ as in (26). Then:
--   1. $g$ is submodular on all subsets of $V$: $g(X) + g(Y) \ge g(X \cap Y) + g(X \cup Y)$ for all $X, Y \subseteq V$ (display (27));
--   2. if $U \subseteq V$ minimizes $g(U) - c(U)$ over all subsets of $V$, then $\overline U \in \mathcal C$ and
--   $$f(\overline U) \le f(T) \qquad \text{for all } T \in \mathcal C,$$
--   that is, $\overline U$ minimizes $f$ over $\mathcal C$.
--
--   Together these say that any algorithm minimizing submodular functions on all subsets of $V$ also minimizes a submodular function given only on a ring family: run it on the submodular function $g - c$ and take the closure of its output.
--
--   **Formalization Note** $f$ is a function on all of `Finset V`, but its values outside $\mathcal C$ never enter $g$, $c$ or the conclusion under the hypotheses. The hypotheses $\emptyset \in \mathcal C$, $V \in \mathcal C$ and $M_u \ne M_v$ are the paper's normalization ("We can assume that $M = \emptyset$, $V \in \mathcal C$, and $M_u \ne M_v$ for all $u \ne v$"); without $M_u \ne M_v$ the set $L_v \cup \{v\}$ in (23) may lie outside $\mathcal C$ and the statement can fail. The paper allows any ordered field; we use $\mathbb R$. The running-time claims of §6 (computing $c$ with $2|V|$ oracle calls, strongly polynomial time) are not formalized.
-- source:
--   Schrijver, A combinatorial algorithm minimizing submodular functions in strongly polynomial time, J. Combin. Theory Ser. B 80 (2000), pp. 353–354, §6, display (27) and last paragraph

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SchrijverSFM_Ring_Setting

namespace SchrijverSFM.Ring

theorem ring_family_reduction {V : Type} [Fintype V] [DecidableEq V]
    (C : Set (Finset V)) (hC : IsRingFamily C) (hempty : ∅ ∈ C) (huniv : Finset.univ ∈ C)
    (hM : ∀ u v : V, u ≠ v → M C u ≠ M C v) (f : Finset V → ℝ) (hf : SubmodularOn C f) :
    NonmonotoneSubmod.Shared.Submodular (g C f) ∧
      ∀ U : Finset V, (∀ W : Finset V, g C f U - csum C f U ≤ g C f W - csum C f W) →
        closure C U ∈ C ∧ ∀ T ∈ C, f (closure C U) ≤ f T := by sorry

end SchrijverSFM.Ring
