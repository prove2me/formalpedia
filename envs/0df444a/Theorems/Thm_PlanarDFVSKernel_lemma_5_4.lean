-- Prove2me | Theorems.Thm_PlanarDFVSKernel_lemma_5_4
-- name    : PlanarDFVSKernel.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:37:54.603683+00:00
-- url     : https://prove2.me/theorems/548f9c66-434f-4225-b1d1-7fbe512d20e9
-- title:
--   Lemma 5.4 — earliest allowed positions respect the records
-- statement:
--   **Lemma 5.4.** Let $(H,\mathcal G,k)$ with $W$, $R$ (the available reverse arcs), $L$ and $\theta$ be as in §5.1, with the structural properties of Lemmas 4.3 and 4.4, and with $H$ weakly connected. Let $T$ be a directed tree with at most $k+1$ edges and $f:V(H)\to V(T)$ a map such that for every base arc $u\to v$ either $f(u)=f(v)$ or $f(u)\to f(v)$ is an edge of $T$, and for every reverse arc $v\to u\in R$ either $f(u)=f(v)$ or $f(u)\to f(v)$ is an edge of $T$. Then there is a map $v\mapsto m_v\in V(T)$ such that
--   1. $m_w=f(w)$ for every $w\in W$;
--   2. if $u,v\notin W$ and $\theta(u)=\theta(v)$, then $m_u=m_v$;
--   3. for every base arc $u\to v$, either $m_u=m_v$ or $m_u\to m_v$ is an edge of $T$; for every reverse arc $v\to u\in R$, either $m_v=m_u$ or $m_u\to m_v$ is an edge of $T$.
--
--   Differences from the source:
--   - generalization: H, W, R, L, θ as in §5.1 (one weakly connected component of the dual instance after Rule 6) → any weakly connected CompressionSetting: acyclic base graph, single-arc ordinary groups, available arcs closing base paths, base arcs covered; no planarity or dual; reason: these are the properties of Lemmas 4.3–4.4 the proof uses (Lemma 4.4's reachability follows from acyclicity); the paper's instance satisfies them
--   - encoding: T with at most k + 1 edges → a directed tree on a finite node type with at most k + 2 nodes; reason: a tree has one node more than edges
-- source:
--   Sheng, Xiao, A Polynomial Kernel for Planar Directed Feedback Vertex Set, arXiv:2609.23669 (held version, sha256 75cfca8f…), Lemma 5.4, p.22 (PDF 23)

import Mathlib
import Definitions.Def_PlanarDFVSKernel_ArcReach
import Definitions.Def_PlanarDFVSKernel_CompressionSetting
import Definitions.Def_PlanarDFVSKernel_DirTree

set_option autoImplicit false

namespace PlanarDFVSKernel

/-- **Lemma 5.4** (Sheng, Xiao, *A Polynomial Kernel for Planar Directed Feedback Vertex Set*, arXiv:2609.23669 (held version, sha256 75cfca8f…), Lemma 5.4, p.22 (PDF 23)): "Let H, W, R, L, and θ be as in Section 5.1,
with the structural properties established in Lemmas 4.3 and 4.4. In particular, every available
reverse arc closes a base path, and every base arc lies on a base path whose reverse belongs to R. Let
T be a directed tree with at most k + 1 edges, and let f : V(H) → V(T) be a map with the following
properties: for every base arc u → v of H, either f(u) = f(v) or f(u) → f(v) is an edge of T; and for
every reverse arc v → u ∈ R, either f(u) = f(v) or f(u) → f(v) is an edge of T. There is a map
v ↦ m_v ∈ V(T) such that: (i) m_w = f(w) for every w ∈ W. (ii) If u, v ∉ W and θ(u) = θ(v), then
m_u = m_v. (iii) For every base arc u → v, either m_u = m_v or m_u → m_v is an edge of T. For every
reverse arc v → u ∈ R, either m_v = m_u or m_u → m_v is an edge of T."

**Formalization Note** The setting is a `CompressionSetting` (acyclic base graph, single-arc
ordinary groups, available arcs closing base paths, base arcs covered) whose base graph is weakly
connected (Section 5.1 works in one component). `W`, `L`'s distances and `θ` are computed from
it with its budget `k`. A reverse arc `v → u` is an available arc `a = (v, u)`. A tree with at most
`k + 1` edges has at most `k + 2` nodes. -/
theorem lemma_5_4 {V : Type*} [Fintype V] [DecidableEq V] (C : CompressionSetting V)
    (hconn : ∀ u v : V, ArcWeakReach C.I.base u v)
    {P : Type*} [Fintype P] (T : DirTree P) (hT : Fintype.card P ≤ C.I.k + 2) (f : V → P)
    (hbase : ∀ a ∈ C.I.base, f a.1 = f a.2 ∨ T.arc (f a.1) (f a.2))
    (hrev : ∀ a : V × V, C.available a → f a.2 = f a.1 ∨ T.arc (f a.2) (f a.1)) :
    ∃ mv : V → P, (∀ w ∈ C.W, mv w = f w) ∧
      (∀ u v : V, u ∉ C.W → v ∉ C.W → C.theta u = C.theta v → mv u = mv v) ∧
      (∀ a ∈ C.I.base, mv a.1 = mv a.2 ∨ T.arc (mv a.1) (mv a.2)) ∧
      (∀ a : V × V, C.available a → mv a.1 = mv a.2 ∨ T.arc (mv a.2) (mv a.1)) := by sorry

end PlanarDFVSKernel
