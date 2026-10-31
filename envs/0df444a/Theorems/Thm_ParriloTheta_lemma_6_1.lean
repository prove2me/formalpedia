-- Prove2me | Theorems.Thm_ParriloTheta_lemma_6_1
-- name    : ParriloTheta.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:28:07.009519+00:00
-- url     : https://prove2.me/theorems/578d4813-5fb8-4748-b159-412dbc8da045
-- title:
--   Lemma 6.1 — columns of a $\mathcal K^{(1)}$-certificate of $M_G$, and the block form (6.1)
-- statement:
--   Let $G=(V,E)$ be a graph with $\alpha=\alpha(G)$, let $\{P(i):i\in V\}$ be a $\mathcal K^{(1)}$-certificate for $M_G$, let $i\in V$, and let $C_l$ denote column $l$ of $P(i)$. Then:
--   1. if $S$ is a stable set of size $\alpha(G)$ with $i\in S$, then $\sum_{j\in S}C_j=0$;
--   2. if $\{i,j\}\in E$ is a critical edge of $G$, then $C_i=C_j$;
--   3. if $\alpha(G\setminus i^\perp)=\alpha(G)-1$ and $\{l,m\}$ is a critical edge of $G\setminus i^\perp$, then $C_l=C_m$;
--   4. if $G$ is critical and $G\setminus i^\perp$ is critical and connected, then
--   $$
--   P(i)=\begin{pmatrix}(\alpha-1)J_{|i^\perp|}&-1\\-1&\frac{1}{\alpha-1}J_{|V\setminus i^\perp|}\end{pmatrix},\qquad(6.1)
--   $$
--   with blocks indexed by $i^\perp$ and $V\setminus i^\perp$.
--
--   The paper states the lemma for graphs of $\vartheta$-rank $1$; the statement here assumes only that the certificate exists.
--
--   **Formalization Note** Column $l$ of $P(i)$ is the vector $r\mapsto P(i)_{rl}$. A node of $G\setminus i^\perp$ is a node of $G$ outside $i^\perp$. Connectedness of $G\setminus i^\perp$ is Mathlib's `Preconnected`, which also admits the empty graph.
--
--   Differences from the source:
--   - generalization: hypothesis ϑ-rank(G) = 1 (and a K⁽¹⁾-certificate {P(i)} for M_G) → only a K⁽¹⁾-certificate {P(i)} for M_G; reason: the proof uses only the certificate; a certificate exists exactly when ϑ-rank(G) ≤ 1 (Lemma 2.2 and (1.7)), so the case ϑ-rank(G) = 1 is included
--   - generalization: G ∖ i⊥ connected, in (6.1) → (delNbhd G i).Preconnected; reason: this also admits an empty G ∖ i⊥, where G is a clique and (6.1) is the zero matrix; every instance with G ∖ i⊥ nonempty is the page's
--   - encoding: V = [n]; columns C_l of P(i) → a finite type V; fun r => P i r l; reason: Lean convention
-- source:
--   Laurent & Vargas, Exactness of Parrilo's conic approximations for copositive matrices and associated low order bounds for the stability number of a graph, arXiv:2109.12876v1, Lemma 6.1 with eq. (6.1), p.18

import Mathlib
import Definitions.Def_ChvatalPolytopes_Separation_AlphaCritical
import Definitions.Def_ParriloTheta_graphMatrix
import Definitions.Def_ParriloTheta_IsK1Cert
import Definitions.Def_ParriloTheta_delNbhd

namespace ParriloTheta

open ChvatalPolytopes.Separation

/-- **Lemma 6.1: columns of a `K^(1)`-certificate of `M_G`.**
Laurent & Vargas, *Exactness of Parrilo's conic approximations for copositive matrices and
associated low order bounds for the stability number of a graph*, arXiv:2109.12876v1, Lemma 6.1 with eq. (6.1), p.18:
"Let G = (V = [n], E) be a graph with ϑ-rank(G) = 1. Let {P(i) : i ∈ V} be a K(1)-certificate for
MG, let i ∈ V and let C1, C2, . . . , Cn denote the columns of the matrix P(i). Then the following
holds. (i) If S is a stable set of size α(G) and i ∈ S, then we have ∑_{j∈S} Cj = 0. (ii) If
{i, j} ∈ E is a critical edge of G then we have Ci = Cj. (iii) If α(G \ i⊥) = α(G) − 1 and
{l, m} ∈ E is a critical edge of G \ i⊥, then we have Cl = Cm. In particular, if G is critical and
G \ i⊥ is critical and connected then the matrix P(i) takes the form
P(i) = ((α − 1)J_{|i⊥|}, −1; −1, (1/(α−1)) J_{|V∖i⊥|}), (6.1) where the blocks are indexed by i⊥
and V ∖ i⊥, respectively."

**Generalization.** The hypothesis "ϑ-rank(G) = 1" is replaced by the existence of the
`K^(1)`-certificate alone (which means ϑ-rank(G) ≤ 1, by Lemma 2.2 and (1.7)); the case
ϑ-rank(G) = 1 is included. "G \ i⊥ connected" is Mathlib's `Preconnected`, which also admits the
empty graph; `Connected` adds nonemptiness. With `V = i⊥` the block `V ∖ i⊥` of (6.1) is empty.

**Formalization Note.** Column `l` of `P(i)` is `fun r => P i r l`. The stable set `S` of size
`α(G)` is `G.IsNIndepSet G.indepNum S`. A node `u` of `G \ i⊥` is a subtype element and
`u.1` the node of `G`. In (6.1), `u ∈ i⊥` means `u = i ∨ G.Adj i u`. The junk value `1/0` is never
reached: a node outside `i⊥` gives a stable pair, so `α(G) ≥ 2` there. -/
theorem lemma_6_1 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : V → Matrix V V ℝ)
    (hP : IsK1Cert (graphMatrix G) P) (i : V) :
    (∀ S : Finset V, G.IsNIndepSet G.indepNum S → i ∈ S →
      ∑ j ∈ S, (fun r => P i r j) = 0) ∧
    (∀ j : V, IsCriticalEdge G s(i, j) → (fun r => P i r i) = (fun r => P i r j)) ∧
    ((delNbhd G i).indepNum = G.indepNum - 1 →
      ∀ l m, IsCriticalEdge (delNbhd G i) s(l, m) → (fun r => P i r l.1) = (fun r => P i r m.1)) ∧
    (IsAlphaCritical G → IsAlphaCritical (delNbhd G i) → (delNbhd G i).Preconnected →
      ∀ u v : V, P i u v =
        if (u = i ∨ G.Adj i u) ∧ (v = i ∨ G.Adj i v) then (G.indepNum : ℝ) - 1
        else if (u = i ∨ G.Adj i u) ∨ (v = i ∨ G.Adj i v) then -1
        else 1 / ((G.indepNum : ℝ) - 1)) := by sorry

end ParriloTheta
