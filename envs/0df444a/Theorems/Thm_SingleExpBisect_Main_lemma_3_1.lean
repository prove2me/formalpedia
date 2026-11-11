-- Prove2me | Theorems.Thm_SingleExpBisect_Main_lemma_3_1
-- name    : SingleExpBisect.Main.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:40:41.445816+00:00
-- url     : https://prove2.me/theorems/c6c7f3d2-2c97-4b74-96dc-52c64a58ed12
-- title:
--   Lemma 3.1 — exact recurrence for Q_{t,R} from the children's boundary coefficients
-- statement:
--   Let $T$ be a rooted tree decomposition of $G$, $k\ge0$, $t$ a node and $R\subseteq B_t$. Then, as Laurent polynomials,
--   $$Q_{t,R}(x,w)=\Big\langle w^{|\delta_{G_t[B_t]}(R)|+\eta_t(R\cap\partial G_t)}\prod_{s\in\mathrm{child}(t)}\Big(w^{-\eta_s(R\cap\partial G_s)}\Big[\prod_{v\in R\cap\partial G_s}y_v\Big]_yZ_s\big(\omega_s^{\partial G_s}(y,x),w\big)\Big)\Big\rangle_{\deg_w\le k}.$$
--
--   Differences from the source:
--   - generalization: T supplied by Theorem 1.1 (adhesion ≤ 2k and (2k,k)-edge-unbreakable bags) → any rooted tree decomposition T of any graph G; reason: the proof (pp. 17–18) uses only the tree-decomposition axioms and (7); the source's T is a special case
--   - encoding: Laurent powers w^{−η_s(·)} → Laurent polynomials AddMonoidAlgebra ℚ (Var n →₀ ℤ); polynomials embedded by toL; ⟨·⟩_{deg_w ≤ k} as truncWL k; reason: the same identity, read in the ring where (8) is written
--   - encoding: V(G_t), ∂G_t, G_t[B_t], child(t) → published T.cone t, T.adhesion t, bagGraph G T t, T.children t on vertex type Fin n; reason: the published definitions are these objects
-- source:
--   Kumabe, Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New Unbreakable Decomposition, arXiv:2611.05982 (October 2026 version; PDF SHA256 6530ce94…6b76541), §3.2, p. 17, Lemma 3.1, (8)

import Mathlib
import Definitions.Def_SingleExpBisect_Main_Graphs
import Definitions.Def_SingleExpBisect_Main_NodeData

open scoped Classical

namespace SingleExpBisect.Main

open MinBisectFPT

/-- Kumabe, *Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New
Unbreakable Decomposition*, arXiv:2611.05982 (October 2026), §3.2, p. 17, Lemma 3.1, (8): for every
node `t` and every `R ⊆ B_t`,
`Q_{t,R}(x, w) = ⟨ w^{|δ_{G_t[B_t]}(R)| + η_t(R ∩ ∂G_t)} · Π_{s ∈ child(t)} ( w^{−η_s(R ∩ ∂G_s)} ·
[Π_{v ∈ R ∩ ∂G_s} y_v]_y Z_s(ω_s^{∂G_s}(y, x), w) ) ⟩_{deg_w ≤ k}`,
as an identity of Laurent polynomials. `G_t[B_t]` is the published `bagGraph G T t`. -/
theorem lemma_3_1 {n : ℕ} (G : SimpleGraph (Fin n)) (T : RootedTD n) (hT : IsRootedTreeDecomp G T)
    (k : ℕ) (t : Fin T.N) (R : Finset (Fin n)) (hR : R ⊆ T.bag t) :
    toL (Qpoly G (T.cone t) (T.bag t) k R) =
      truncWL k
        (wPow ((cutSize (bagGraph G T t) R + etaNode G T t (R ∩ T.adhesion t) : ℕ) : ℤ) *
          ∏ s ∈ T.children t,
            (wPow (-((etaNode G T s (R ∩ T.adhesion s) : ℕ) : ℤ)) *
              toL (yCoeff (R ∩ T.adhesion s) (Zomega G T k s)))) := by sorry

end SingleExpBisect.Main
