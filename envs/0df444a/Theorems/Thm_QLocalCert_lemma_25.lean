-- Prove2me | Theorems.Thm_QLocalCert_lemma_25
-- name    : QLocalCert.lemma_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:41:46.528126+00:00
-- url     : https://prove2.me/theorems/4110ba65-aa3a-4366-9405-75486cd788d0
-- title:
--   Lemma 25 — tags are rigid: $\mathrm{Tag}(i)\cong_{\mathrm{rt}}\mathrm{Tag}(j)$ iff $i=j$, and the only tag branches are those at the $a_i$
-- statement:
--   Let $\mu\ge1$, $N\ge8$ even, $z,z'\in\{0,1\}^N$ balanced, and $T=T^{\mathrm{tr}}_{N,\mu}(z,z')$.
--   1. For all $i,j\in\{0,\dots,N/2\}$, $\mathrm{Tag}(i)\cong_{\mathrm{rt}}\mathrm{Tag}(j)$ if and only if $i=j$.
--   2. For every vertex $v$ of $T$, every neighbour $u$ of $v$ and every $i\in\{0,\dots,N/2\}$, the branch of $T$ at $v$ containing $u$ is isomorphic as a rooted tree to $\mathrm{Tag}(i)$ if and only if $v$ is an index-$i$ vertex $a_i$, on either side, and $u$ is the root of the tag attached to $v$.
--
--   This rigidity lets an isomorphism of two such trees be read gadget by gadget (Lemma 26).
--
--   Differences from the source:
--   - encoding: the index-i vertex a_i on either side and the root of its tag → the vertices .left (.a i), .right (.a i) and .left (.tag i .s), .right (.tag i .s); reason: vertex names of the tree's vertex type
--   - encoding: branch of T at v containing u, rooted at u → the subgraph induced on the component of T − v containing u, with a rooted isomorphism mapping u to s; reason: the definition on p.36
-- source:
--   Jauregui, Miyamoto, Quantum Advantage in Local Certification of Graph Properties, STOC 2027 submission (manuscript sha256 b707143b1ab5511bef4c2b77e1b803f28b32cced25a008516898fd11d28c0451), Lemma 25, p.36

import Mathlib
import Definitions.Def_QLocalCert_Ttr
import Definitions.Def_QLocalCert_BranchRootedIso

set_option autoImplicit false

namespace QLocalCert

/-- **Lemma 25** (p.36). "Let µ ≥ 1 and even N ≥ 8, let z, z′ ∈ {0, 1}^N have Hamming weight N/2,
and denote T := T^tr_{N,µ}(z, z′). The following properties hold.
1. For any i, j ∈ {0, . . . , N/2}, Tag(i) ≅_rt Tag(j) if and only if i = j.
2. For every vertex v of T, every neighbor u of v, and every i ∈ {0, . . . , N/2}, the branch of T at
v containing u is isomorphic as a rooted tree to Tag(i) if and only if v is an index-i vertex aᵢ, on
either side, and u is the root of the tag attached to v."

Source: B. Jauregui, M. Miyamoto, *Quantum Advantage in Local Certification of Graph Properties*,
STOC 2027 submission (manuscript sha256 b707143b…0c51), Lemma 25, p.36 (branch: p.36; ≅_rt: §2, p.14).

**Formalization Note.** Tags are rooted at `TagV.s`. In (2), the index-`i` vertices are
`.left (.a i)` and `.right (.a i)`, and the root of the tag attached to `aᵢ` is the tag vertex
`s` of that side, `.left (.tag i .s)` resp. `.right (.tag i .s)`. -/
theorem lemma_25 (μ N : ℕ) (hμ : 1 ≤ μ) (hN : Even N) (h8 : 8 ≤ N) (z z' : Fin N → Bool)
    (hz : Balanced z) (hz' : Balanced z') :
    (∀ i j : Fin (N / 2 + 1), RootedIso (Tag N i) .s (Tag N j) .s ↔ i = j) ∧
    (∀ v u : TV N μ (runLengths z) (runLengths z'), (Ttr N μ z z').Adj v u →
      ∀ i : Fin (N / 2 + 1), BranchRootedIso (Ttr N μ z z') v u (Tag N i) .s ↔
        ((v = .left (.a i) ∧ u = .left (.tag i .s)) ∨
          (v = .right (.a i) ∧ u = .right (.tag i .s)))) := by sorry

end QLocalCert
